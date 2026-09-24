import OperatorPhaseRetrieval.MathlibImports

noncomputable section

/-!
# Three-phase separation (paper Lemma 3.2)

The proof uses a direct degree-two root calculation, with no polynomial
approximation or phase-retrieval assumptions.
-/

namespace OperatorPhaseRetrieval

def IsPhase (z : ℂ) : Prop := ‖z‖ = 1

def MagnitudeMatch (r s u v : ℝ) : Prop :=
  (r = u ∧ s = v) ∨ (r = v ∧ s = u)

theorem quadratic_three_roots (A B C x y z : ℂ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : A + B*x + C*x^2 = 0)
    (hy : A + B*y + C*y^2 = 0)
    (hz : A + B*z + C*z^2 = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by
  have h₁ : B + C*(x+y) = 0 := by
    apply (mul_eq_zero.mp (show (x-y)*(B+C*(x+y)) = 0 by
      linear_combination hx - hy)).resolve_left (sub_ne_zero.mpr hxy)
  have h₂ : B + C*(x+z) = 0 := by
    apply (mul_eq_zero.mp (show (x-z)*(B+C*(x+z)) = 0 by
      linear_combination hx - hz)).resolve_left (sub_ne_zero.mpr hxz)
  have hC : C = 0 := by
    apply (mul_eq_zero.mp (show C*(y-z) = 0 by
      linear_combination h₁ - h₂)).resolve_right (sub_ne_zero.mpr hyz)
  have hB : B = 0 := by simpa [hC] using h₁
  have hA : A = 0 := by simpa [hC, hB] using hx
  exact ⟨hA, hB, hC⟩

theorem phase_mul_conj {η : ℂ} (hη : IsPhase η) : η * star η = 1 := by
  have hn : Complex.normSq η = 1 := by
    rw [Complex.normSq_eq_norm_sq, hη, one_pow]
  simpa [Complex.normSq_eq_conj_mul_self, mul_comm] using
    congrArg (fun r : ℝ => (r : ℂ)) hn

theorem scalar_expansion (a b c d η : ℂ) (hη : IsPhase η)
    (h : ‖a + η*b‖ = ‖c + η*d‖) :
    (a * star b - c * star d) +
      ((‖a‖^2 + ‖b‖^2 - ‖c‖^2 - ‖d‖^2 : ℝ) : ℂ) * η +
      star (a * star b - c * star d) * η^2 = 0 := by
  have hsq : (star (a+η*b))*(a+η*b) -
      (star (c+η*d))*(c+η*d) = 0 := by
    have hh := congrArg (fun r : ℝ => ((r^2 : ℝ) : ℂ)) h
    simpa only [← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self, starRingEnd_apply, sub_eq_zero] using hh
  have hu := phase_mul_conj hη
  simp only [star_add, star_mul] at hsq
  simp only [Complex.ofReal_sub, Complex.ofReal_add,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
    star_sub, star_mul, star_star]
  simp only [starRingEnd_apply]
  linear_combination η * hsq -
    (star b * b * η - star d * d * η + a * star b - c * star d) * hu

theorem scalar_invariants (a b c d : ℂ) (η : Fin 3 → ℂ)
    (hη : ∀ j, IsPhase (η j)) (hinj : Function.Injective η)
    (h : ∀ j, ‖a + η j*b‖ = ‖c + η j*d‖) :
    ‖a‖^2 + ‖b‖^2 = ‖c‖^2 + ‖d‖^2 ∧ a*star b = c*star d := by
  have hs := quadratic_three_roots
    (a*star b-c*star d)
    ((‖a‖^2+‖b‖^2-‖c‖^2-‖d‖^2 : ℝ) : ℂ)
    (star (a*star b-c*star d)) (η 0) (η 1) (η 2)
    (fun he => (by decide : (0 : Fin 3) ≠ 1) (hinj he))
    (fun he => (by decide : (0 : Fin 3) ≠ 2) (hinj he))
    (fun he => (by decide : (1 : Fin 3) ≠ 2) (hinj he))
    (scalar_expansion a b c d (η 0) (hη 0) (h 0))
    (scalar_expansion a b c d (η 1) (hη 1) (h 1))
    (scalar_expansion a b c d (η 2) (hη 2) (h 2))
  constructor
  · have he := congrArg Complex.re hs.2.1
    simp only [Complex.ofReal_re, Complex.zero_re] at he
    linarith
  · exact sub_eq_zero.mp hs.1

theorem pair_from_sum_product (r s u v : ℝ)
    (hsum : r+s = u+v) (hprod : r*s = u*v) :
    (r=u ∧ s=v) ∨ (r=v ∧ s=u) := by
  have he : (r-u)*(r-v) = 0 := by linear_combination r*hsum - hprod
  rcases mul_eq_zero.mp he with he | he
  · left; constructor <;> linarith
  · right; constructor <;> linarith

theorem pair_from_invariants (r s u v : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hadd : r^2+s^2 = u^2+v^2) (hmul : r^2*s^2 = u^2*v^2) :
    MagnitudeMatch r s u v := by
  rcases pair_from_sum_product (r^2) (s^2) (u^2) (v^2) hadd hmul with h | h
  · left; constructor <;> nlinarith [h.1, h.2]
  · right; constructor <;> nlinarith [h.1, h.2]

/-- Lemma 3.2, including the unordered-pair and mixed-product conclusions. -/
theorem three_phase (a b c d : ℂ) (η : Fin 3 → ℂ)
    (hη : ∀ j, IsPhase (η j)) (hinj : Function.Injective η)
    (h : ∀ j, ‖a + η j*b‖ = ‖c + η j*d‖) :
    MagnitudeMatch ‖a‖ ‖b‖ ‖c‖ ‖d‖ ∧ a*star b = c*star d := by
  obtain ⟨hs, hp⟩ := scalar_invariants a b c d η hη hinj h
  refine ⟨pair_from_invariants _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hs ?_, hp⟩
  have hn := congrArg norm hp
  simp only [norm_mul, norm_star] at hn
  calc
    ‖a‖^2 * ‖b‖^2 = (‖a‖*‖b‖)^2 := by ring
    _ = (‖c‖*‖d‖)^2 := congrArg (fun x : ℝ => x^2) hn
    _ = ‖c‖^2 * ‖d‖^2 := by ring

theorem matching_cancel_first {r s u v : ℝ}
    (h : MagnitudeMatch r s u v) (he : r=u) : s=v := by
  rcases h with h | h
  · exact h.2
  · exact h.2.trans (he.symm.trans h.1)

theorem matching_cancel_second {r s u v : ℝ}
    (h : MagnitudeMatch r s u v) (he : s=v) : r=u := by
  rcases h with h | h
  · exact h.1
  · exact h.1.trans (he.symm.trans h.2)

theorem matching_cross_first {r s u v : ℝ}
    (h : MagnitudeMatch r s u v) (he : r≠u) : r=v ∧ s=u := by
  exact h.resolve_left (fun hd => he hd.1)

theorem matching_cross_second {r s u v : ℝ}
    (h : MagnitudeMatch r s u v) (he : s≠v) : r=v ∧ s=u := by
  exact h.resolve_left (fun hd => he hd.2)

end OperatorPhaseRetrieval

end
