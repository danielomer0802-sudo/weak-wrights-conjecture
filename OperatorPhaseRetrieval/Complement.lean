import OperatorPhaseRetrieval.AmplificationTheorem

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory

/-! Functional-calculus construction of the complement in Proposition 5.1. -/

open scoped CStarAlgebra
namespace OperatorPhaseRetrieval

theorem exists_complement {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : H →L[ℂ] H) (hC : IsSelfAdjoint C) (hsmall : ‖C‖^2 < (1:ℝ)/2) :
    ∃ D : H →L[ℂ] H, IsSelfAdjoint D ∧ Commute C D ∧ C*C+D*D=1 := by
  rcases subsingleton_or_nontrivial H with htr | htr
  · let := htr
    refine ⟨0, IsSelfAdjoint.zero _, ?_, ?_⟩
    · exact Commute.zero_right C
    · exact Subsingleton.elim _ _
  · let := htr
    let f : ℝ → ℝ := fun t => Real.sqrt (1-t^2)
    have hf : Continuous f := (continuous_const.sub (continuous_id.pow 2)).sqrt
    let D : H →L[ℂ] H := cfc f C
    have hD : IsSelfAdjoint D := cfc_predicate f C
    have hc : Commute C D := by
      have hh := cfc_commute_cfc (fun t : ℝ => t) f C
      rw [cfc_id' ℝ C hC] at hh
      exact hh
    have he : Set.EqOn (fun t : ℝ => t*t+f t*f t) (fun _ => 1) (spectrum ℝ C) := by
      intro t ht
      have hn : ‖t‖ ≤ ‖C‖ := spectrum.norm_le_norm_of_mem ht
      have hsq : t^2 ≤ ‖C‖^2 := by
        have hh := pow_le_pow_left₀ (norm_nonneg t) hn 2
        simpa only [Real.norm_eq_abs, sq_abs] using hh
      have hp : 0 ≤ 1-t^2 := by linarith
      dsimp [f]
      nlinarith [Real.sq_sqrt hp]
    refine ⟨D, hD, hc, ?_⟩
    calc
      C*C+D*D = cfc (fun t : ℝ => t*t+f t*f t) C := by
        rw [cfc_add C (fun t : ℝ => t*t) (fun t => f t*f t)
          (continuous_id.mul continuous_id).continuousOn (hf.mul hf).continuousOn,
          cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) C,
          cfc_mul f f C hf.continuousOn hf.continuousOn, cfc_id' ℝ C hC]
      _ = cfc (fun _ : ℝ => 1) C := cfc_congr he
      _ = 1 := cfc_const_one ℝ C hC

open MeasureTheory

/-- Proposition 5.1. Positivity is unnecessary once C is self-adjoint and small. -/
theorem amplification {X : Type*} [MeasurableSpace X] {μ : Measure X} [NeZero μ]
    (C : L2 μ →L[ℂ] L2 μ) (hC : IsSelfAdjoint C)
    (hsmall : ‖C‖^2 < (1:ℝ)/2) (hrigid : ModulusRigid C) :
    ∃ P : SumL2 (L2 μ) →L[ℂ] SumL2 (L2 μ), IsOrthogonalProjection P ∧
      ∀ η : Fin 3 → ℂ, (∀ j, IsPhase (η j)) → Function.Injective η →
        (∀ j, IsUnitary (phaseFamily P (η j))) ∧
        ∀ x y, (∀ j, PairModEq (phaseFamily P (η j) x) (phaseFamily P (η j) y)) →
          PhaseRelated x y := by
  obtain ⟨D, hD, hcomm, hsq⟩ := exists_complement C hC hsmall
  exact ⟨blockProjection C D,
    amplification_with_complement C D hC hD hcomm hsq hsmall hrigid⟩

end OperatorPhaseRetrieval

end
