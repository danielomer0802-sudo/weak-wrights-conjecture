import OperatorPhaseRetrieval.ThreePhase

noncomputable section

open MeasureTheory Filter

/-! Algebra of the single-projection phase family, used in Theorem 2.1 and Corollary 2.2. -/

namespace OperatorPhaseRetrieval
section Algebra
variable {A : Type*} [Ring A] [Algebra ℂ A]

def phaseFamily (P : A) (η : ℂ) : A := 1 + (η-1) • P

@[simp] theorem phaseFamily_one (P : A) : phaseFamily P 1 = 1 := by
  simp [phaseFamily]

theorem phaseFamily_mul (P : A) (hP : P*P=P) (η ξ : ℂ) :
    phaseFamily P η * phaseFamily P ξ = phaseFamily P (η*ξ) := by
  simp only [phaseFamily, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hP]
  module

theorem phaseFamily_commute (P : A) (hP : P*P=P) (η ξ : ℂ) :
    Commute (phaseFamily P η) (phaseFamily P ξ) := by
  show phaseFamily P η * phaseFamily P ξ = phaseFamily P ξ * phaseFamily P η
  rw [phaseFamily_mul P hP, phaseFamily_mul P hP, mul_comm η ξ]

theorem phaseFamily_pow (P : A) (hP : P*P=P) (η : ℂ) (n : ℕ) :
    (phaseFamily P η)^n = phaseFamily P (η^n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, phaseFamily_mul P hP, pow_succ]

theorem phaseFamily_cube (P : A) (hP : P*P=P) {η : ℂ} (hη : η^3=1) :
    (phaseFamily P η)^3 = 1 := by
  rw [phaseFamily_pow P hP, hη, phaseFamily_one]

variable [StarRing A] [StarModule ℂ A]

def IsOrthogonalProjection (P : A) : Prop := P*P=P ∧ star P=P
def IsUnitary (U : A) : Prop := star U*U=1 ∧ U*star U=1

theorem phaseFamily_star (P : A) (hP : star P=P) (η : ℂ) :
    star (phaseFamily P η) = phaseFamily P (star η) := by
  simp [phaseFamily, hP]

theorem phaseFamily_unitary (P : A) (hP : IsOrthogonalProjection P)
    {η : ℂ} (hη : IsPhase η) : IsUnitary (phaseFamily P η) := by
  have hu := phase_mul_conj hη
  constructor
  · rw [phaseFamily_star P hP.2, phaseFamily_mul P hP.1, mul_comm, hu]
    exact phaseFamily_one P
  · rw [phaseFamily_star P hP.2, phaseFamily_mul P hP.1, hu]
    exact phaseFamily_one P

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem conjugate_projection (P V : A) (hP : IsOrthogonalProjection P)
    (hV : IsUnitary V) : IsOrthogonalProjection (V*P*star V) := by
  constructor
  · calc
      (V*P*star V)*(V*P*star V) = V*P*(star V*V)*P*star V := by
        simp only [mul_assoc]
      _ = V*P*star V := by rw [hV.1, mul_one]; simp [mul_assoc, hP.1]
  · simp only [star_mul, star_star, hP.2, mul_assoc]

omit [StarModule ℂ A] in
theorem conjugate_phaseFamily (P V : A) (hV : IsUnitary V) (η : ℂ) :
    phaseFamily (V*P*star V) η = V*phaseFamily P η*star V := by
  simp only [phaseFamily, mul_add, mul_one, add_mul,
    mul_smul_comm, smul_mul_assoc, hV.2]

end Algebra

section Norm
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projection_norm_le_one (P : H →L[ℂ] H) (hP : IsOrthogonalProjection P) :
    ‖P‖ ≤ 1 := by
  have h : ‖P‖ = ‖P‖ * ‖P‖ := by
    calc
      ‖P‖ = ‖star P * P‖ := by rw [hP.2, hP.1]
      _ = ‖P‖ * ‖P‖ := CStarRing.norm_star_mul_self
  nlinarith [norm_nonneg P]

theorem phaseFamily_norm_sub (P : H →L[ℂ] H) (η : ℂ) :
    ‖phaseFamily P η - 1‖ = ‖η-1‖ * ‖P‖ := by
  simp [phaseFamily, norm_smul]

theorem phaseFamily_norm_sub_le (P : H →L[ℂ] H) (hP : ‖P‖ ≤ 1) (η : ℂ) :
    ‖phaseFamily P η - 1‖ ≤ ‖η-1‖ := by
  rw [phaseFamily_norm_sub]
  nlinarith [norm_nonneg (η-1)]

theorem unitary_norm (U : H →L[ℂ] H) (hU : IsUnitary U) (x : H) : ‖U x‖=‖x‖ := by
  apply U.norm_map_of_mem_unitary
  exact hU

theorem projection_phase_norm_bound (P : H →L[ℂ] H)
    (hP : IsOrthogonalProjection P) (η : ℂ) :
    ‖phaseFamily P η - 1‖ ≤ ‖η-1‖ :=
  phaseFamily_norm_sub_le P (projection_norm_le_one P hP) η

end Norm
end OperatorPhaseRetrieval

end
