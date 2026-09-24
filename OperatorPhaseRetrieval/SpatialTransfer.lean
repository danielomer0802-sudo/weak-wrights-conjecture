import OperatorPhaseRetrieval.Complement
import OperatorPhaseRetrieval.PolynomialBasis

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped Topology

/-!
# Transport and assembly

This module proves transport by a supplied modulus-preserving unitary. It does
not assume that arbitrary Hilbert-space isomorphisms preserve pointwise moduli.
The required spatial unitary is constructed in SpatialExistence.lean.
-/

open MeasureTheory
namespace OperatorPhaseRetrieval
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def ProjectionWorks (R : H → H → Prop) : Prop :=
  ∃ P : H →L[ℂ] H, IsOrthogonalProjection P ∧
    ∀ η : Fin 3 → ℂ, (∀ j, IsPhase (η j)) → Function.Injective η →
      (∀ j, IsUnitary (phaseFamily P (η j))) ∧
      ∀ f g, (∀ j, R (phaseFamily P (η j) f) (phaseFamily P (η j) g)) →
        PhaseRelated f g

def transport (W : H ≃ₗᵢ[ℂ] G) (P : G →L[ℂ] G) : H →L[ℂ] H :=
  W.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L P ∘L
    W.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] theorem transport_apply (W : H ≃ₗᵢ[ℂ] G) (P : G →L[ℂ] G) (f : H) :
    transport W P f = W.symm (P (W f)) := rfl

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] theorem map_transport (W : H ≃ₗᵢ[ℂ] G) (P : G →L[ℂ] G) (f : H) :
    W (transport W P f) = P (W f) := by simp

theorem transport_projection (W : H ≃ₗᵢ[ℂ] G) {P : G →L[ℂ] G}
    (hP : IsOrthogonalProjection P) : IsOrthogonalProjection (transport W P) := by
  constructor
  · ext f
    have hp := congrArg (fun T : G →L[ℂ] G => T (W f)) hP.1
    simp only [mul_apply_eq_comp] at hp ⊢
    simp only [transport_apply, W.apply_symm_apply, hp]
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro f g
    change inner (𝕜 := ℂ) (transport W P f) g = inner (𝕜 := ℂ) f (transport W P g)
    have hs : IsSelfAdjoint P := hP.2
    calc
      _ = inner (𝕜 := ℂ) (W (transport W P f)) (W g) := (W.inner_map_map _ _).symm
      _ = inner (𝕜 := ℂ) (P (W f)) (W g) := by rw [map_transport]
      _ = inner (𝕜 := ℂ) (W f) (P (W g)) := hs.isSymmetric _ _
      _ = inner (𝕜 := ℂ) (W f) (W (transport W P g)) := by rw [map_transport]
      _ = _ := W.inner_map_map _ _

omit [CompleteSpace H] [CompleteSpace G] in
theorem map_phaseFamily_transport (W : H ≃ₗᵢ[ℂ] G) (P : G →L[ℂ] G)
    (η : ℂ) (f : H) :
    W (phaseFamily (transport W P) η f) = phaseFamily P η (W f) := by
  simp [phaseFamily, add_apply, smul_apply]

theorem transfer_projectionWorks (W : H ≃ₗᵢ[ℂ] G)
    {R : H → H → Prop} {S : G → G → Prop}
    (hW : ∀ f g, S (W f) (W g) ↔ R f g) (hS : ProjectionWorks S) :
    ProjectionWorks R := by
  obtain ⟨P, hP, hretr⟩ := hS
  have hQ := transport_projection W hP
  refine ⟨transport W P, hQ, ?_⟩
  intro η hη hinj
  refine ⟨fun j => phaseFamily_unitary _ hQ (hη j), ?_⟩
  intro f g hm
  have hmeasure : ∀ j, S (phaseFamily P (η j) (W f)) (phaseFamily P (η j) (W g)) := by
    intro j
    have hh := (hW _ _).2 (hm j)
    simpa only [map_phaseFamily_transport] using hh
  obtain ⟨ω, hω, he⟩ := (hretr η hη hinj).2 (W f) (W g) hmeasure
  refine ⟨ω, hω, W.injective ?_⟩
  simpa only [W.map_smul] using he

abbrev RealL2 := L2 (volume : Measure ℝ)

/-- Exact unconditional target of paper Theorem 2.1, proved by `main` in Main.lean. -/
def MainStatement : Prop := ProjectionWorks (@ModEq ℝ _ volume)

/-- Section 6.2 assembly, conditional on the analytic and spatial constructions.

The hypotheses are discharged by RigidModel.lean and SpatialExistence.lean;
Main.lean instantiates this assembly theorem.
-/
theorem main_of_rigid_spatial_model {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [NeZero μ]
    (C : L2 μ →L[ℂ] L2 μ) (hC : IsSelfAdjoint C) (hsmall : ‖C‖ ≤ (1:ℝ)/8)
    (hrigid : ModulusRigid C) (W : RealL2 ≃ₗᵢ[ℂ] SumL2 (L2 μ))
    (hW : ∀ f g, PairModEq (W f) (W g) ↔ ModEq f g) : MainStatement := by
  have hsq : ‖C‖^2 < (1:ℝ)/2 := by nlinarith [norm_nonneg C]
  exact transfer_projectionWorks W hW (amplification C hC hsq hrigid)

/-- Assembly from polynomial density and a spatial unitary. Both inputs have
unconditional constructions in RigidModel.lean and SpatialExistence.lean. -/
theorem main_of_polynomial_density_spatial {μ : Measure ℂ} [NeZero μ]
    (hμ : μ ≪ volume)
    (hm : ∀ p : Polynomial ℂ, MemLp (fun z => p.eval z) 2 μ)
    (hd : (polynomialL2 hm).range.topologicalClosure = ⊤)
    (W : RealL2 ≃ₗᵢ[ℂ] SumL2 (L2 μ))
    (hW : ∀ f g, PairModEq (W f) (W g) ↔ ModEq f g) : MainStatement := by
  obtain ⟨C,hC,hn,_,_,hr⟩ := exists_rigid_of_polynomial_density hμ hm hd
  exact main_of_rigid_spatial_model C hC.isSelfAdjoint hn hr W hW

end OperatorPhaseRetrieval

end
