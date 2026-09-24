import OperatorPhaseRetrieval.L2

noncomputable section

open MeasureTheory Filter

/-!
# The direct/cross matching argument of Proposition 5.1

`amplification_core` proves the a.e. argument on the actual L2 space. Its explicit
operator hypotheses are the norm domination and injectivity of a complement D.
Its data hypotheses are precisely the pointwise invariants and norm identity
obtained from the unitary block construction. No analytic existence theorem is
asserted here.
-/

open MeasureTheory Filter
namespace OperatorPhaseRetrieval
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def PointwiseFacts (C D : L2 μ →L[ℂ] L2 μ) (a b a' b' : L2 μ) : Prop :=
  ∀ᵐ t ∂μ,
    MagnitudeMatch ‖C a t‖ ‖D b t‖ ‖C a' t‖ ‖D b' t‖ ∧
    MagnitudeMatch ‖D a t‖ ‖C b t‖ ‖D a' t‖ ‖C b' t‖ ∧
    C a t * star (D b t) = C a' t * star (D b' t)

/-- Pointwise information from the three actual L2 measurement pairs. -/
theorem pointwise_from_measurements (C D : L2 μ →L[ℂ] L2 μ)
    (a b a' b' : L2 μ) (η : Fin 3 → ℂ)
    (hη : ∀ j, IsPhase (η j)) (hinj : Function.Injective η)
    (h₁ : ∀ j, ModEq (C a - η j • D b) (C a' - η j • D b'))
    (h₂ : ∀ j, ModEq (D a + η j • C b) (D a' + η j • C b')) :
    PointwiseFacts C D a b a' b' := by
  have hm₁ : ∀ j, ∀ᵐ t ∂μ,
      ‖C a t + η j * (-D b t)‖ = ‖C a' t + η j * (-D b' t)‖ := by
    intro j
    filter_upwards [h₁ j, Lp.coeFn_sub (C a) (η j • D b),
      Lp.coeFn_sub (C a') (η j • D b'),
      Lp.coeFn_smul (η j) (D b), Lp.coeFn_smul (η j) (D b')]
      with t ht h₁ h₂ h₃ h₄
    simpa only [h₁, h₂, Pi.sub_apply, h₃, h₄, Pi.smul_apply,
      smul_eq_mul, mul_neg, ← sub_eq_add_neg] using ht
  have hm₂ : ∀ j, ∀ᵐ t ∂μ,
      ‖D a t + η j * C b t‖ = ‖D a' t + η j * C b' t‖ := by
    intro j
    filter_upwards [h₂ j, Lp.coeFn_add (D a) (η j • C b),
      Lp.coeFn_add (D a') (η j • C b'),
      Lp.coeFn_smul (η j) (C b), Lp.coeFn_smul (η j) (C b')]
      with t ht h₁ h₂ h₃ h₄
    simpa only [h₁, h₂, Pi.add_apply, h₃, h₄, Pi.smul_apply, smul_eq_mul] using ht
  have hall₁ : ∀ᵐ t ∂μ, ∀ j, ‖C a t + η j * (-D b t)‖ =
      ‖C a' t + η j * (-D b' t)‖ := (ae_all_iff).2 hm₁
  have hall₂ : ∀ᵐ t ∂μ, ∀ j, ‖D a t + η j * C b t‖ =
      ‖D a' t + η j * C b' t‖ := (ae_all_iff).2 hm₂
  filter_upwards [hall₁, hall₂] with t ht₁ ht₂
  obtain ⟨hm₁, hp⟩ := three_phase (C a t) (-D b t) (C a' t) (-D b' t)
    η hη hinj ht₁
  obtain ⟨hm₂, _⟩ := three_phase (D a t) (C b t) (D a' t) (C b' t)
    η hη hinj ht₂
  exact ⟨by simpa only [norm_neg] using hm₁, hm₂,
    by simpa only [star_neg, mul_neg, neg_inj] using hp⟩

theorem direct_a [NeZero μ] {C D : L2 μ →L[ℂ] L2 μ}
    (hC : ModulusRigid C) {a b a' b' : L2 μ}
    (h : PointwiseFacts C D a b a' b') (ha : PhaseRelated a a') :
    PhaseRelated b b' := by
  apply rigid_global hC
  have hd := modEq_of_phaseRelated (phaseRelated_map D ha)
  filter_upwards [h, hd] with t ht hd
  exact matching_cancel_first ht.2.1 hd

theorem direct_b [NeZero μ] {C D : L2 μ →L[ℂ] L2 μ}
    (hC : ModulusRigid C) {a b a' b' : L2 μ}
    (h : PointwiseFacts C D a b a' b') (hb : PhaseRelated b b') :
    PhaseRelated a a' := by
  apply rigid_global hC
  have hd := modEq_of_phaseRelated (phaseRelated_map D hb)
  filter_upwards [h, hd] with t ht hd
  exact matching_cancel_second ht.1 hd

theorem common_phase {C D : L2 μ →L[ℂ] L2 μ}
    (hC : ModulusRigid C) (hD : Function.Injective D)
    {a b a' b' : L2 μ} (h : PointwiseFacts C D a b a' b')
    (ha : PhaseRelated a a') (hb : PhaseRelated b b') :
    ∃ ω : ℂ, IsPhase ω ∧ a' = ω • a ∧ b' = ω • b := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  by_cases haz : a = 0
  · exact ⟨β, hβ, by simp [haz], rfl⟩
  by_cases hbz : b = 0
  · exact ⟨α, hα, rfl, by simp [hbz]⟩
  have hDb : D b ≠ 0 := by
    intro hz
    apply hbz
    apply hD
    simpa using hz
  have hp := (h.and (rigid_nonzero_ae hC haz)).and
    ((ae_smul_map C α a).and (ae_smul_map D β b))
  obtain ⟨t, ht, hbt⟩ := nonzero_support_exists hDb hp
  have he : α = β := by
    apply synchronize_phases hβ ht.1.2 hbt
    simpa only [ht.2.1, ht.2.2] using ht.1.1.2.2
  exact ⟨α, hα, rfl, by rw [he]⟩

theorem opNorm_sq_bound (C : L2 μ →L[ℂ] L2 μ) (f : L2 μ) :
    ‖C f‖^2 ≤ ‖C‖^2 * ‖f‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (C f)) (C.le_opNorm f) 2
  simpa only [mul_pow] using h

/-- The crossed branch is impossible except at zero. -/
theorem cross_zero {C D : L2 μ →L[ℂ] L2 μ}
    (hC : ModulusRigid C) (hsmall : ‖C‖^2 < (1:ℝ)/2)
    (hD : ∀ f, (1-‖C‖^2)*‖f‖^2 ≤ ‖D f‖^2)
    {a b a' b' : L2 μ} (h : PointwiseFacts C D a b a' b')
    (hnorm : ‖a‖^2+‖b‖^2 = ‖a'‖^2+‖b'‖^2)
    (ha : ¬ PhaseRelated a a') (hb : ¬ PhaseRelated b b') :
    a = 0 ∧ b = 0 ∧ a' = 0 ∧ b' = 0 := by
  have hc₁ : ModEq (D b) (C a') := by
    filter_upwards [h, rigid_separated hC ha] with t ht hnt
    exact (matching_cross_first ht.1 hnt).2
  have hc₂ : ModEq (D a) (C b') := by
    filter_upwards [h, rigid_separated hC hb] with t ht hnt
    exact (matching_cross_second ht.2.1 hnt).1
  have hn₁ := norm_eq_of_modEq hc₁
  have hn₂ := norm_eq_of_modEq hc₂
  have hd₁ := hD a
  have hd₂ := hD b
  have hu₁ := opNorm_sq_bound C a'
  have hu₂ := opNorm_sq_bound C b'
  rw [hn₁] at hd₂
  rw [hn₂] at hd₁
  have he : ‖a‖^2+‖b‖^2 = 0 := by
    have he' : (1-2*‖C‖^2)*(‖a‖^2+‖b‖^2) ≤ 0 := by
      nlinarith [mul_nonneg (sq_nonneg ‖C‖) (sq_nonneg ‖a'‖),
        mul_nonneg (sq_nonneg ‖C‖) (sq_nonneg ‖b'‖)]
    have hp : 0 < 1-2*‖C‖^2 := by linarith
    have hn : 0 ≤ ‖a‖^2+‖b‖^2 := by positivity
    nlinarith
  have ha0 : ‖a‖ = 0 := by nlinarith [sq_nonneg ‖b‖]
  have hb0 : ‖b‖ = 0 := by nlinarith [sq_nonneg ‖a‖]
  have ha'0 : ‖a'‖ = 0 := by nlinarith [sq_nonneg ‖b'‖]
  have hb'0 : ‖b'‖ = 0 := by nlinarith [sq_nonneg ‖a'‖]
  exact ⟨norm_eq_zero.mp ha0, norm_eq_zero.mp hb0,
    norm_eq_zero.mp ha'0, norm_eq_zero.mp hb'0⟩

/-- Proposition 5.1, Steps 2-3, after the explicit block operator identities. -/
theorem amplification_core [NeZero μ] {C D : L2 μ →L[ℂ] L2 μ}
    (hC : ModulusRigid C) (hsmall : ‖C‖^2 < (1:ℝ)/2)
    (hDinj : Function.Injective D)
    (hD : ∀ f, (1-‖C‖^2)*‖f‖^2 ≤ ‖D f‖^2)
    {a b a' b' : L2 μ} (h : PointwiseFacts C D a b a' b')
    (hnorm : ‖a‖^2+‖b‖^2 = ‖a'‖^2+‖b'‖^2) :
    ∃ ω : ℂ, IsPhase ω ∧ a' = ω • a ∧ b' = ω • b := by
  by_cases ha : PhaseRelated a a'
  · exact common_phase hC hDinj h ha (direct_a hC h ha)
  by_cases hb : PhaseRelated b b'
  · exact common_phase hC hDinj h (direct_b hC h hb) hb
  obtain ⟨rfl, rfl, rfl, rfl⟩ := cross_zero hC hsmall hD h hnorm ha hb
  exact ⟨1, norm_one, by simp, by simp⟩

end OperatorPhaseRetrieval

end
