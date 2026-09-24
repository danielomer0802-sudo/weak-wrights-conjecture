import OperatorPhaseRetrieval.UniformAlgebra

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

/-! Logistic approximation of coordinate cuts inside the polynomial closure. -/
open Set Filter
open scoped Topology
namespace OperatorPhaseRetrieval

theorem one_add_ne_zero_of_norm_le_half {w : ℂ} (hw : ‖w‖ ≤ 1/2) : 1+w ≠ 0 := by
  intro h
  have he : w = -1 := by linear_combination h
  rw [he] at hw
  norm_num at hw

theorem logistic_small_bound {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖w / (1+w)‖ ≤ 2 * ‖w‖ := by
  have hb : (1:ℝ)/2 ≤ ‖1+w‖ := by
    have h := norm_sub_norm_le (1:ℂ) (-w)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at h
    linarith
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖1+w‖)).mpr
  nlinarith [norm_nonneg w]

theorem logistic_left_bound {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖(1+w)⁻¹ - 1‖ ≤ 2 * ‖w‖ := by
  have he : (1+w)⁻¹ - 1 = -(w/(1+w)) := by
    field_simp [one_add_ne_zero_of_norm_le_half hw]
    ring
  rw [he, norm_neg]
  exact logistic_small_bound hw

theorem logistic_right_bound {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w⁻¹‖ ≤ 1/2) :
    ‖(1+w)⁻¹‖ ≤ 2 * ‖w⁻¹‖ := by
  have he : (1+w)⁻¹ = w⁻¹/(1+w⁻¹) := by
    field_simp
    ring
  rw [he]
  exact logistic_small_bound hw

theorem exp_one_add_ne_zero {w : ℂ} (hw : w.re ≠ 0) : 1 + Complex.exp w ≠ 0 := by
  intro he
  have hv : Complex.exp w = -1 := by linear_combination he
  have hn := congrArg norm hv
  rw [Complex.norm_exp] at hn
  norm_num at hn
  exact hw (by simpa using hn)

variable (K : Set ℂ) [CompactSpace K] [Nonempty K]

theorem real_gap (f : C(K,ℂ)) (hf : ∀ z, (f z).re ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ z, d ≤ |(f z).re| := by
  obtain ⟨z, -, hz⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    ((Complex.continuous_re.comp f.continuous).abs.continuousOn)
  exact ⟨|(f z).re|, abs_pos.mpr (hf z), fun x => hz (mem_univ x)⟩

def realCut (f : C(K,ℂ)) (hf : ∀ z, (f z).re ≠ 0) : C(K,ℂ) := by
  classical
  have ho : IsOpen {z | (f z).re < 0} := isOpen_lt (Complex.continuous_re.comp f.continuous) continuous_const
  have hc : IsClosed {z | (f z).re < 0} := by
    have he : {z | (f z).re < 0} = {z | (f z).re ≤ 0} := by
      ext z
      exact lt_iff_le_and_ne.trans (and_iff_left (hf z))
    rw [he]
    exact isClosed_le (Complex.continuous_re.comp f.continuous) continuous_const
  exact ⟨fun z => if (f z).re < 0 then 1 else 0,
    (show IsClopen {z | (f z).re < 0} from ⟨hc,ho⟩).continuous_indicator continuous_const⟩

omit [CompactSpace ↑K] [Nonempty ↑K] in
theorem realCut_apply (f : C(K,ℂ)) (hf : ∀ z, (f z).re ≠ 0) (z : K) :
    realCut K f hf z = if (f z).re < 0 then 1 else 0 := rfl

omit [CompactSpace ↑K] [Nonempty ↑K] in
theorem logistic_uniform_bound (f : C(K,ℂ)) (hf : ∀ z, (f z).re ≠ 0)
    {d N : ℝ} (_hd : 0 < d) (hN : 0 < N) (hgap : ∀ z, d ≤ |(f z).re|)
    (hsmall : Real.exp (-N*d) ≤ 1/2) (z : K) :
    ‖(1 + Complex.exp ((N:ℂ) * f z))⁻¹ - realCut K f hf z‖ ≤
      2 * Real.exp (-N*d) := by
  rw [realCut_apply]
  by_cases hz : (f z).re < 0
  · rw [if_pos hz]
    have hb : ‖Complex.exp ((N:ℂ) * f z)‖ ≤ Real.exp (-N*d) := by
      rw [Complex.norm_exp, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      apply Real.exp_le_exp.mpr
      have hg := hgap z
      rw [abs_of_neg hz] at hg
      nlinarith
    exact (logistic_left_bound (hb.trans hsmall)).trans (by linarith)
  · rw [if_neg hz, sub_zero]
    have hb : ‖(Complex.exp ((N:ℂ) * f z))⁻¹‖ ≤ Real.exp (-N*d) := by
      rw [← Complex.exp_neg, Complex.norm_exp, Complex.neg_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      apply Real.exp_le_exp.mpr
      have hg := hgap z
      rw [abs_of_nonneg (le_of_not_gt hz)] at hg
      nlinarith
    exact (logistic_right_bound (Complex.exp_ne_zero _) (hb.trans hsmall)).trans (by linarith)

theorem realCut_mem_uniformClosure (hK : IsPreconnected Kᶜ) (f : C(K,ℂ))
    (hfm : f ∈ uniformPolynomialClosure K) (hf : ∀ z, (f z).re ≠ 0) :
    realCut K f hf ∈ uniformPolynomialClosure K := by
  classical
  change realCut K f hf ∈ (uniformPolynomialClosure K : Set C(K,ℂ))
  rw [← (uniformPolynomialClosure_closed K).closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨d,hd,hgap⟩ := real_gap K f hf
  have ht : Tendsto (fun N : ℝ => Real.exp (-N*d)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const hd) using 1
    ext N
    simp only [Function.comp_apply, id_eq, neg_mul]
  obtain ⟨N,hN,hsmall,heps⟩ := ((eventually_gt_atTop (0:ℝ)).and
    ((ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).and
      (ht.eventually (gt_mem_nhds (show (0:ℝ)<ε/4 by positivity))))).exists
  obtain ⟨e,hem,he⟩ := uniformClosure_exp K ((N:ℂ) • f)
    ((uniformPolynomialClosure K).smul_mem hfm _)
  have hden : ∀ z, (1+e) z ≠ 0 := by
    intro z
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, he,
      ContinuousMap.smul_apply, smul_eq_mul]
    apply exp_one_add_ne_zero
    simpa using mul_ne_zero hN.ne' (hf z)
  obtain ⟨r,hrm,hr⟩ := uniformClosure_inverse K hK (1+e)
    ((uniformPolynomialClosure K).add_mem (uniformPolynomialClosure K).one_mem hem) hden
  refine ⟨r,hrm,?_⟩
  have hb : ‖r - realCut K f hf‖ ≤ 2*Real.exp (-N*d) := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro z
    simp only [ContinuousMap.sub_apply, hr, ContinuousMap.add_apply,
      ContinuousMap.one_apply, he, ContinuousMap.smul_apply, smul_eq_mul]
    exact logistic_uniform_bound K f hf hd hN hgap hsmall.le z
  rw [dist_comm, dist_eq_norm]
  linarith

end OperatorPhaseRetrieval

end
