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

/-!
# Arbitrarily small unitary phase steps

An elementary Cayley parameter avoids needing exponential periodicity:
eta(t) = (1+it)/(1-it). For t>0, 1, eta(t), eta(t)^2 are distinct,
and their distances from 1 are bounded by 2t and 4t.
-/

namespace OperatorPhaseRetrieval

def cayley (t : ℝ) : ℂ := (1+(t:ℂ)*Complex.I)/(1-(t:ℂ)*Complex.I)

theorem cayley_den_ne_zero (t : ℝ) : (1-(t:ℂ)*Complex.I : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp at hr

theorem cayley_isPhase (t : ℝ) : IsPhase (cayley t) := by
  have hc : star (1-(t:ℂ)*Complex.I) = 1+(t:ℂ)*Complex.I := by simp
  have hn : ‖1+(t:ℂ)*Complex.I‖=‖1-(t:ℂ)*Complex.I‖ := by rw [← hc, norm_star]
  unfold IsPhase cayley
  rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr (cayley_den_ne_zero t))]

theorem cayley_ne_one {t : ℝ} (ht : 0<t) : cayley t ≠ 1 := by
  intro h
  have hh := (div_eq_iff (cayley_den_ne_zero t)).mp h
  have hi := congrArg Complex.im hh
  simp at hi
  linarith

theorem cayley_ne_neg_one (t : ℝ) : cayley t ≠ -1 := by
  intro h
  have hh := (div_eq_iff (cayley_den_ne_zero t)).mp h
  have hr := congrArg Complex.re hh
  norm_num at hr

theorem cayley_sq_ne_one {t : ℝ} (ht : 0<t) : (cayley t)^2 ≠ 1 := by
  intro h
  rcases sq_eq_one_iff.mp h with h | h
  · exact cayley_ne_one ht h
  · exact cayley_ne_neg_one t h

theorem cayley_sq_ne_self {t : ℝ} (ht : 0<t) : (cayley t)^2 ≠ cayley t := by
  intro h
  apply cayley_ne_one ht
  apply mul_right_cancel₀ (phase_ne_zero (cayley_isPhase t))
  simpa only [pow_two, one_mul] using h

theorem cayley_sub_one (t : ℝ) : cayley t-1 =
    (2*(t:ℂ)*Complex.I)/(1-(t:ℂ)*Complex.I) := by
  unfold cayley
  field_simp [cayley_den_ne_zero t]
  ring

theorem cayley_norm_sub_one {t : ℝ} (ht : 0<t) : ‖cayley t-1‖ ≤ 2*t := by
  have hd : 1 ≤ ‖1-(t:ℂ)*Complex.I‖ := by
    have h := Complex.abs_re_le_norm (1-(t:ℂ)*Complex.I)
    simpa using h
  rw [cayley_sub_one, norm_div, norm_mul, norm_mul]
  norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  exact div_le_self (by positivity) hd

theorem phase_square_norm_sub_one {η : ℂ} (hη : IsPhase η) :
    ‖η^2-1‖ ≤ 2*‖η-1‖ := by
  calc
    ‖η^2-1‖ = ‖(η-1)*η+(η-1)‖ := by congr 1; ring
    _ ≤ ‖(η-1)*η‖+‖η-1‖ := norm_add_le _ _
    _ = 2*‖η-1‖ := by rw [norm_mul, show ‖η‖=1 from hη]; ring

def powerPhases (η : ℂ) : Fin 3 → ℂ := ![1,η,η^2]

theorem powerPhases_unit {η : ℂ} (hη : IsPhase η) : ∀ j, IsPhase (powerPhases η j) := by
  intro j
  fin_cases j
  · exact norm_one
  · exact hη
  · change ‖η^2‖=1
    rw [norm_pow, show ‖η‖=1 from hη, one_pow]

theorem cayleyPhases_injective {t : ℝ} (ht : 0<t) :
    Function.Injective (powerPhases (cayley t)) := by
  have h01 : powerPhases (cayley t) 0 ≠ powerPhases (cayley t) 1 := Ne.symm (cayley_ne_one ht)
  have h02 : powerPhases (cayley t) 0 ≠ powerPhases (cayley t) 2 := Ne.symm (cayley_sq_ne_one ht)
  have h12 : powerPhases (cayley t) 1 ≠ powerPhases (cayley t) 2 := Ne.symm (cayley_sq_ne_self ht)
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

/-- Explicit scalar choices for both strict near-identity bounds. -/
theorem small_phase_triple (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℂ, IsPhase η ∧ Function.Injective (powerPhases η) ∧
      ‖η-1‖ < ε ∧ ‖η^2-1‖ < ε := by
  let t := ε/8
  have ht : 0<t := by dsimp [t]; positivity
  have hb := cayley_norm_sub_one ht
  have hs := phase_square_norm_sub_one (cayley_isPhase t)
  refine ⟨cayley t, cayley_isPhase t, cayleyPhases_injective ht, ?_, ?_⟩ <;>
    dsimp [t] at hb hs ⊢ <;> linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Near-identity assertion of Corollary 2.2, given a working projection. -/
theorem near_identity_of_projection (R : H → H → Prop) (P : H →L[ℂ] H)
    (hP : IsOrthogonalProjection P)
    (hretr : ∀ η : Fin 3 → ℂ, (∀ j, IsPhase (η j)) → Function.Injective η →
      ∀ f g, (∀ j, R (phaseFamily P (η j) f) (phaseFamily P (η j) g)) → PhaseRelated f g)
    (ε : ℝ) (hε : 0<ε) :
    ∃ U : H →L[ℂ] H, IsUnitary U ∧ ‖U-1‖<ε ∧ ‖U^2-1‖<ε ∧
      ∀ f g, R f g → R (U f) (U g) → R ((U^2) f) ((U^2) g) → PhaseRelated f g := by
  obtain ⟨η, hη, hinj, hn₁, hn₂⟩ := small_phase_triple ε hε
  let U := phaseFamily P η
  refine ⟨U, phaseFamily_unitary P hP hη,
    (projection_phase_norm_bound P hP η).trans_lt hn₁, ?_, ?_⟩
  · dsimp [U]
    rw [phaseFamily_pow P hP.1]
    exact (projection_phase_norm_bound P hP (η^2)).trans_lt hn₂
  · intro f g h₀ h₁ h₂
    apply hretr (powerPhases η) (powerPhases_unit hη) hinj f g
    intro j
    fin_cases j
    · simpa [powerPhases] using h₀
    · exact h₁
    · change R (phaseFamily P (η^2) f) (phaseFamily P (η^2) g)
      rw [← phaseFamily_pow P hP.1]
      exact h₂

end OperatorPhaseRetrieval

end
