import OperatorPhaseRetrieval.L2
import OperatorPhaseRetrieval.Projection

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped Topology

/-! An explicit order-three phase and the algebraic order-three consequence. -/

namespace OperatorPhaseRetrieval

def cubePhase : ℂ := ⟨-1/2, Real.sqrt 3/2⟩

theorem cubePhase_isPhase : IsPhase cubePhase := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hn : Complex.normSq cubePhase = 1 := by
    simp only [Complex.normSq_apply, cubePhase]
    nlinarith
  unfold IsPhase
  rw [Complex.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg cubePhase]

theorem cubePhase_quadratic : cubePhase^2+cubePhase+1=0 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  apply Complex.ext <;>
    simp [cubePhase, pow_two, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem cubePhase_cube : cubePhase^3=1 := by
  linear_combination (cubePhase-1)*cubePhase_quadratic

theorem cubePhase_ne_one : cubePhase ≠ 1 := by
  intro h
  have hh := congrArg Complex.re h
  norm_num [cubePhase] at hh

theorem cubePhase_sq_ne_one : cubePhase^2 ≠ 1 := by
  intro h
  apply cubePhase_ne_one
  have hc := cubePhase_cube
  rw [pow_succ, h, one_mul] at hc
  exact hc

theorem cubePhase_sq_ne_self : cubePhase^2 ≠ cubePhase := by
  intro h
  have hn := phase_ne_zero cubePhase_isPhase
  apply cubePhase_ne_one
  apply (mul_right_cancel₀ hn)
  simpa only [pow_two, one_mul] using h

def cubePhases : Fin 3 → ℂ := ![1, cubePhase, cubePhase^2]

theorem cubePhases_unit : ∀ j, IsPhase (cubePhases j) := by
  intro j
  fin_cases j
  · exact norm_one
  · exact cubePhase_isPhase
  · change ‖cubePhase^2‖=1
    rw [norm_pow, show ‖cubePhase‖=1 from cubePhase_isPhase, one_pow]

theorem cubePhases_injective : Function.Injective cubePhases := by
  have h01 : cubePhases 0 ≠ cubePhases 1 := Ne.symm cubePhase_ne_one
  have h02 : cubePhases 0 ≠ cubePhases 2 := Ne.symm cubePhase_sq_ne_one
  have h12 : cubePhases 1 ≠ cubePhases 2 := Ne.symm cubePhase_sq_ne_self
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact (h01 h).elim
  · exact (h02 h).elim
  · exact (h01 h.symm).elim
  · rfl
  · exact (h12 h).elim
  · exact (h02 h.symm).elim
  · exact (h12 h.symm).elim
  · rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The first assertion of Corollary 2.2, conditional only on a working projection.
The existential working projection on L2(R) remains the main construction goal.
-/
theorem order_three_of_projection (R : H → H → Prop) (P : H →L[ℂ] H)
    (hP : IsOrthogonalProjection P)
    (hretr : ∀ η : Fin 3 → ℂ, (∀ j, IsPhase (η j)) → Function.Injective η →
      ∀ f g, (∀ j, R (phaseFamily P (η j) f) (phaseFamily P (η j) g)) →
        PhaseRelated f g) :
    ∃ U : H →L[ℂ] H, IsUnitary U ∧ U^3=1 ∧
      ∀ f g, R f g → R (U f) (U g) → R ((U^2) f) ((U^2) g) → PhaseRelated f g := by
  let U := phaseFamily P cubePhase
  refine ⟨U, phaseFamily_unitary P hP cubePhase_isPhase,
    phaseFamily_cube P hP.1 cubePhase_cube, ?_⟩
  intro f g h₀ h₁ h₂
  apply hretr cubePhases cubePhases_unit cubePhases_injective f g
  intro j
  fin_cases j
  · simpa [cubePhases] using h₀
  · exact h₁
  · change R (phaseFamily P (cubePhase^2) f) (phaseFamily P (cubePhase^2) g)
    rw [← phaseFamily_pow P hP.1]
    exact h₂

end OperatorPhaseRetrieval

end
