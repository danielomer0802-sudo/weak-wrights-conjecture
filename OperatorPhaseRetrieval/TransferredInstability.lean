import OperatorPhaseRetrieval.Main
import OperatorPhaseRetrieval.MagnitudeDistance

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory Set
open Set
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-! Quantitative instability on the original L2 space, for the same projection
that gives phase retrieval. -/
open MeasureTheory
namespace OperatorPhaseRetrieval

/-- Uniform continuity of recovery modulo a constant phase, on the unit sphere. -/
def L2UniformPhaseRecovery {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : ι → L2 μ →L[ℂ] L2 μ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ f g : L2 μ, ‖f‖ = 1 → ‖g‖ = 1 →
      (∀ j, ‖magnitude (T j f)-magnitude (T j g)‖ < δ) →
      ∃ ω : ℂ, IsPhase ω ∧ ‖f-ω • g‖ < ε

theorem uniformRecovery_of_transport {X Y ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (W : L2 ν ≃ₗᵢ[ℂ] SumL2 (L2 μ))
    (hW : ∀ f g, PairModEq (W f) (W g) ↔ ModEq f g)
    (P : SumL2 (L2 μ) →L[ℂ] SumL2 (L2 μ)) (η : ι → ℂ)
    (h : L2UniformPhaseRecovery (fun j => phaseFamily (transport W P) (η j))) :
    UniformPhaseRecovery (fun j => phaseFamily P (η j)) := by
  intro ε hε
  obtain ⟨δ,hδ,hr⟩ := h ε hε
  refine ⟨δ,hδ,fun x y hx hy hd => ?_⟩
  have hdata : ∀ j,
      ‖magnitude (phaseFamily (transport W P) (η j) (W.symm x))-
        magnitude (phaseFamily (transport W P) (η j) (W.symm y))‖ < δ := by
    intro j
    rw [← pair_spatial_magnitudeDistance W hW]
    simpa only [map_phaseFamily_transport,W.apply_symm_apply] using hd j
  obtain ⟨ω,hω,hclose⟩ := hr (W.symm x) (W.symm y)
    (by simpa using hx) (by simpa using hy) hdata
  refine ⟨ω,hω,?_⟩
  simpa only [← W.symm.map_smul,← W.symm.map_sub,W.symm.norm_map] using hclose

theorem transported_no_uniform_recovery {X Y ι : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (W : L2 ν ≃ₗᵢ[ℂ] SumL2 (L2 μ))
    (hW : ∀ f g, PairModEq (W f) (W g) ↔ ModEq f g)
    (D : L2 μ →L[ℂ] L2 μ) (b : HilbertBasis ℕ ℂ (L2 μ))
    {w : ℕ → ℝ} (hw : Summable w) (hD : IsSelfAdjoint D)
    (hcomm : Commute (diagonalSmoothing b w) D)
    (hsq : diagonalSmoothing b w * diagonalSmoothing b w + D*D=1)
    (η : ι → ℂ) (hη : ∀ j, IsPhase (η j)) :
    ¬ L2UniformPhaseRecovery (fun j =>
      phaseFamily (transport W (blockProjection (diagonalSmoothing b w) D)) (η j)) := by
  intro h
  exact diagonal_no_uniform_phase_recovery D b hw hD hcomm hsq η hη
    (uniformRecovery_of_transport W hW _ η h)

/-- Theorem 2.1 and Remark 6.3 for one and the same projection. -/
theorem main_with_instability :
    ∃ P : RealL2 →L[ℂ] RealL2, IsOrthogonalProjection P ∧
      ∀ η : Fin 3 → ℂ, (∀ j, IsPhase (η j)) → Function.Injective η →
        (∀ j, IsUnitary (phaseFamily P (η j))) ∧
        (∀ f g, (∀ j, ModEq (phaseFamily P (η j) f) (phaseFamily P (η j) g)) →
          PhaseRelated f g) ∧
        ¬ L2UniformPhaseRecovery (fun j => phaseFamily P (η j)) := by
  obtain ⟨μ,hfin,hμ0,hμv,hm,hd⟩ := exists_polynomial_dense_measure
  let : IsFiniteMeasure μ := hfin
  let : NeZero μ := ⟨hμ0⟩
  let : NullSingletonClass μ := ⟨fun z => hμv (measure_singleton z)⟩
  obtain ⟨b,p,hp⟩ := polynomial_hilbertBasis_of_dense hμv hm hd
  let C := diagonalSmoothing b (smoothingWeight p)
  have hw := smoothingWeight_summable p
  have hC : IsSelfAdjoint C := diagonalSmoothing_selfAdjoint b hw
  have hn : ‖C‖ ≤ (1:ℝ)/8 :=
    (diagonalSmoothing_norm_le b hw (fun n => (smoothingWeight_pos p n).le)).trans
      (smoothingWeight_tsum_le p)
  have hs : ‖C‖^2 < (1:ℝ)/2 := by nlinarith [norm_nonneg C]
  obtain ⟨D,hD,hcomm,hsq⟩ := exists_complement C hC hs
  have hr := polynomialSmoothing_rigid hμv b p hp
  have hP := amplification_with_complement C D hC hD hcomm hsq hs hr
  obtain ⟨W,hW⟩ := exists_double_spatial_unitary μ (volume : Measure ℝ)
  let P := blockProjection C D
  let Q := transport W P
  have hQ : IsOrthogonalProjection Q := transport_projection W hP.1
  refine ⟨Q,hQ,fun η hη hi => ⟨fun j => phaseFamily_unitary Q hQ (hη j),?_,?_⟩⟩
  · intro f g hm
    have hd : ∀ j, PairModEq (phaseFamily P (η j) (W f)) (phaseFamily P (η j) (W g)) := by
      intro j
      have hh := (hW _ _).mpr (hm j)
      simpa only [Q,map_phaseFamily_transport] using hh
    obtain ⟨ω,hω,he⟩ := (hP.2 η hη hi).2 (W f) (W g) hd
    exact ⟨ω,hω,W.injective (by simpa only [W.map_smul] using he)⟩
  · exact transported_no_uniform_recovery W hW D b hw hD hcomm hsq η hη

end OperatorPhaseRetrieval

end
