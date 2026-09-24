import OperatorPhaseRetrieval.Amplification
import OperatorPhaseRetrieval.BlockRotation

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace

/-!
# Amplification with an explicit square-root complement

The conclusion of Proposition 5.1 follows from C, D satisfying the spectral
identities used in its Step 1. `Complement.lean` constructs D by functional
calculus and removes this intermediate hypothesis in the theorem `amplification`.
-/

open MeasureTheory
open scoped InnerProductSpace
namespace OperatorPhaseRetrieval

section Complement
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem complement_norm_identity (C D : H →L[ℂ] H)
    (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D) (hsq : C*C+D*D=1) (f : H) :
    ‖C f‖^2 + ‖D f‖^2 = ‖f‖^2 := by
  have hc := ContinuousLinearMap.isSelfAdjoint_iff'.mp hC
  have hd := ContinuousLinearMap.isSelfAdjoint_iff'.mp hD
  rw [C.apply_norm_sq_eq_inner_adjoint_right, D.apply_norm_sq_eq_inner_adjoint_right,
    hc, hd]
  have hs := congrArg (fun T : H →L[ℂ] H => T f) hsq
  simp only [add_apply, mul_apply_eq_comp,
    one_apply_eq_self] at hs
  change (inner (𝕜 := ℂ) f (C (C f))).re + (inner (𝕜 := ℂ) f (D (D f))).re = _
  rw [← Complex.add_re, ← inner_add_right, hs]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) f

end Complement

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def PairModEq (x y : SumL2 (L2 μ)) : Prop := ModEq x.fst y.fst ∧ ModEq x.snd y.snd

theorem norm_eq_of_pairModEq {x y : SumL2 (L2 μ)} (h : PairModEq x y) : ‖x‖=‖y‖ := by
  have h₁ := norm_eq_of_modEq h.1
  have h₂ := norm_eq_of_modEq h.2
  have hx := WithLp.prod_norm_sq_eq_of_L2 x
  have hy := WithLp.prod_norm_sq_eq_of_L2 y
  rw [h₁, h₂] at hx
  nlinarith [norm_nonneg x, norm_nonneg y]

theorem complement_lower_bound (C D : L2 μ →L[ℂ] L2 μ)
    (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D) (hsq : C*C+D*D=1) (f : L2 μ) :
    (1-‖C‖^2)*‖f‖^2 ≤ ‖D f‖^2 := by
  have hi := complement_norm_identity C D hC hD hsq f
  have hb := opNorm_sq_bound C f
  nlinarith

theorem complement_injective (C D : L2 μ →L[ℂ] L2 μ)
    (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D) (hsq : C*C+D*D=1)
    (hsmall : ‖C‖^2 < (1:ℝ)/2) : Function.Injective D := by
  have hker : ∀ f, D f = 0 → f = 0 := by
    intro f hf
    have hb := complement_lower_bound C D hC hD hsq f
    rw [hf, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hb
    have hzero : ‖f‖ = 0 := by
      nlinarith [sq_nonneg ‖f‖]
    exact norm_eq_zero.mp hzero
  intro f g hfg
  apply sub_eq_zero.mp
  apply hker
  simp [map_sub, hfg]

/-- All three unitary measurements retrieve phase once a complement is supplied. -/
theorem amplification_with_complement [NeZero μ]
    (C D : L2 μ →L[ℂ] L2 μ) (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D)
    (hcomm : Commute C D) (hsq : C*C+D*D=1)
    (hsmall : ‖C‖^2 < (1:ℝ)/2) (hrigid : ModulusRigid C) :
    IsOrthogonalProjection (blockProjection C D) ∧
    ∀ (η : Fin 3 → ℂ), (∀ j, IsPhase (η j)) → Function.Injective η →
      (∀ j, IsUnitary (phaseFamily (blockProjection C D) (η j))) ∧
      ∀ x y : SumL2 (L2 μ),
        (∀ j, PairModEq (phaseFamily (blockProjection C D) (η j) x)
          (phaseFamily (blockProjection C D) (η j) y)) → PhaseRelated x y := by
  have hP := blockProjection_isProjection C D hC hD hcomm hsq
  refine ⟨hP, ?_⟩
  intro η hη hinj
  have hU : ∀ j, IsUnitary (phaseFamily (blockProjection C D) (η j)) :=
    fun j => phaseFamily_unitary _ hP (hη j)
  refine ⟨hU, ?_⟩
  intro x y hm
  let V := blockRotation C D
  have hV : IsUnitary V := block_unitary C D hC hD hcomm hsq
  let u := star V x
  let v := star V y
  have hVu : V u = x := congrArg (fun T : SumL2 (L2 μ) →L[ℂ] SumL2 (L2 μ) => T x) hV.2
  have hVv : V v = y := congrArg (fun T : SumL2 (L2 μ) →L[ℂ] SumL2 (L2 μ) => T y) hV.2
  have hmeasure : ∀ j,
      ModEq (C u.fst - η j • D u.snd) (C v.fst - η j • D v.snd) ∧
      ModEq (D u.fst + η j • C u.snd) (D v.fst + η j • C v.snd) := by
    intro j
    have h := hm j
    rw [← hVu, ← hVv] at h
    change PairModEq (phaseFamily (blockProjection C D) (η j) (blockRotation C D u))
      (phaseFamily (blockProjection C D) (η j) (blockRotation C D v)) at h
    rw [block_measurement C D hC hD hcomm hsq,
      block_measurement C D hC hD hcomm hsq] at h
    exact h
  have hxy : ‖x‖=‖y‖ := by
    have hn := norm_eq_of_pairModEq (hm 0)
    simpa only [unitary_norm _ (hU 0)] using hn
  have huv : ‖u.fst‖^2+‖u.snd‖^2 = ‖v.fst‖^2+‖v.snd‖^2 := by
    rw [← WithLp.prod_norm_sq_eq_of_L2, ← WithLp.prod_norm_sq_eq_of_L2]
    have hnu : ‖u‖=‖x‖ := by rw [← unitary_norm V hV u, hVu]
    have hnv : ‖v‖=‖y‖ := by rw [← unitary_norm V hV v, hVv]
    rw [hnu, hnv, hxy]
  have hp := pointwise_from_measurements C D u.fst u.snd v.fst v.snd η hη hinj
    (fun j => (hmeasure j).1) (fun j => (hmeasure j).2)
  obtain ⟨ω, hω, h₁, h₂⟩ := amplification_core hrigid hsmall
    (complement_injective C D hC hD hsq hsmall)
    (complement_lower_bound C D hC hD hsq) hp huv
  have hvu : v = ω • u := sum_ext h₁ h₂
  refine ⟨ω, hω, ?_⟩
  rw [← hVu, ← hVv, hvu, V.map_smul]

end OperatorPhaseRetrieval

end
