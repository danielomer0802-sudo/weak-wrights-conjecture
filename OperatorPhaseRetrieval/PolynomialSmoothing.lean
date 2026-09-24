import OperatorPhaseRetrieval.DiagonalSmoothing
import OperatorPhaseRetrieval.AnalyticUniqueness

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped Topology

/-! # Entire extensions of polynomial diagonal smoothing

This construction works for any actual polynomial Hilbert basis. The missing
polynomial-density theorem is not built into a typeclass or hidden axiom.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorPhaseRetrieval

def polynomialBound (p : Polynomial ℂ) (R : ℝ) : ℝ :=
  max 0 (Classical.choose ((isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    p.differentiable.continuous.continuousOn))

theorem polynomialBound_nonneg (p : Polynomial ℂ) (R : ℝ) :
    0 ≤ polynomialBound p R := le_max_left _ _

theorem polynomial_eval_le_bound (p : Polynomial ℂ) {R : ℝ} {z : ℂ}
    (hz : ‖z‖ ≤ R) : ‖p.eval z‖ ≤ polynomialBound p R := by
  apply le_trans _ (le_max_right _ _)
  apply Classical.choose_spec ((isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    p.differentiable.continuous.continuousOn)
  simpa using hz

/-- A slightly faster decay than the paper's choice makes the elementary
sum-of-operator-norms bound at most 1/8. -/
def smoothingWeight (p : ℕ → Polynomial ℂ) (n : ℕ) : ℝ :=
  ((1/2 : ℝ)^n / 16) / (1 + polynomialBound (p n) ((n : ℝ) + 2))

theorem smoothingWeight_pos (p : ℕ → Polynomial ℂ) (n : ℕ) :
    0 < smoothingWeight p n := by
  unfold smoothingWeight
  have := polynomialBound_nonneg (p n) ((n : ℝ)+2)
  positivity

theorem smoothingWeight_le (p : ℕ → Polynomial ℂ) (n : ℕ) :
    smoothingWeight p n ≤ (1/2 : ℝ)^n / 16 := by
  unfold smoothingWeight
  apply div_le_self (by positivity)
  linarith [polynomialBound_nonneg (p n) ((n : ℝ)+2)]

theorem smoothingWeight_summable (p : ℕ → Polynomial ℂ) : Summable (smoothingWeight p) := by
  apply Summable.of_nonneg_of_le (fun n => (smoothingWeight_pos p n).le)
    (smoothingWeight_le p)
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2 : ℝ) < 1)).div_const 16

theorem smoothingWeight_tsum_le (p : ℕ → Polynomial ℂ) :
    ∑' n, smoothingWeight p n ≤ (1:ℝ)/8 := by
  have hg : Summable (fun n : ℕ => (1/2 : ℝ)^n / 16) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2 : ℝ) < 1)).div_const 16
  have h := (smoothingWeight_summable p).tsum_le_tsum (smoothingWeight_le p) hg
  calc
    _ ≤ ∑' n : ℕ, (1/2 : ℝ)^n / 16 := h
    _ = (1:ℝ)/8 := by
      rw [tsum_div_const, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

theorem smoothingWeight_mul_bound (p : ℕ → Polynomial ℂ) (n : ℕ) :
    smoothingWeight p n * polynomialBound (p n) ((n : ℝ)+2) ≤ (1/2 : ℝ)^n / 16 := by
  unfold smoothingWeight
  have hM := polynomialBound_nonneg (p n) ((n : ℝ)+2)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [show 0 ≤ (1/2 : ℝ)^n / 16 by positivity]

def polynomialSeries (p : ℕ → Polynomial ℂ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n, (smoothingWeight p n : ℂ) * a n * (p n).eval z

theorem polynomialSeries_majorant (p : ℕ → Polynomial ℂ) (a : ℕ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (ha : ∀ n, ‖a n‖ ≤ B) (N : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n z, ‖z‖ < (N : ℝ)+2 →
      ‖(smoothingWeight p n : ℂ) * a n * (p n).eval z‖ ≤ u n := by
  let u : ℕ → ℝ := fun n => if n < N then
    smoothingWeight p n * B * polynomialBound (p n) ((N : ℝ)+2)
    else B * ((1/2 : ℝ)^n / 16)
  refine ⟨u, ?_, ?_⟩
  · apply Summable.congr_atTop
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2 : ℝ) < 1)).div_const 16
        |>.mul_left B)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [u, not_lt.mpr hn]
  · intro n z hz
    have hw := (smoothingWeight_pos p n).le
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    by_cases hn : n < N
    · simp only [u, if_pos hn]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha n) hw)
        (polynomial_eval_le_bound (p n) hz.le) (norm_nonneg _) (mul_nonneg hw hB)
    · have hN : N ≤ n := Nat.le_of_not_gt hn
      have hzn : ‖z‖ ≤ (n : ℝ)+2 := hz.le.trans (by exact_mod_cast Nat.add_le_add_right hN 2)
      have hp := polynomial_eval_le_bound (p n) hzn
      simp only [u, if_neg hn]
      calc
        smoothingWeight p n * ‖a n‖ * ‖(p n).eval z‖ ≤
            smoothingWeight p n * B * polynomialBound (p n) ((n : ℝ)+2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (ha n) hw) hp
            (norm_nonneg _) (mul_nonneg hw hB)
        _ = B * (smoothingWeight p n * polynomialBound (p n) ((n : ℝ)+2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (smoothingWeight_mul_bound p n) hB

theorem polynomialSeries_entire (p : ℕ → Polynomial ℂ) (a : ℕ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (ha : ∀ n, ‖a n‖ ≤ B) :
    AnalyticOnNhd ℂ (polynomialSeries p a) univ := by
  apply Complex.analyticOnNhd_univ_iff_differentiable.mpr
  intro z
  obtain ⟨N,hN⟩ := exists_nat_gt ‖z‖
  obtain ⟨u,hu,hub⟩ := polynomialSeries_majorant p a hB ha N
  have hd := Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n => ((p n).differentiable.const_mul _).differentiableOn)
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) ((N : ℝ)+2)))
    (fun n w hw => hub n w (by simpa using hw))
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds (by
    simpa using (show ‖z‖ < (N : ℝ)+2 by linarith)))

theorem polynomialSeries_hasSum (p : ℕ → Polynomial ℂ) (a : ℕ → ℂ)
    {B : ℝ} (hB : 0 ≤ B) (ha : ∀ n, ‖a n‖ ≤ B) (z : ℂ) :
    HasSum (fun n => (smoothingWeight p n : ℂ) * a n * (p n).eval z)
      (polynomialSeries p a z) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ‖z‖
  obtain ⟨u,hu,hub⟩ := polynomialSeries_majorant p a hB ha N
  exact (Summable.of_norm_bounded hu (fun n => hub n z (by linarith))).hasSum

theorem hilbert_coefficient_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (b : HilbertBasis ℕ ℂ H) (x : H) (n : ℕ) :
    ‖b.repr x n‖ ≤ ‖x‖ := by
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (b.repr x) n

/-- The representatives of finite L2 sums agree a.e. with the pointwise sums. -/
theorem l2_coeFn_finset_sum {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (s : Finset ℕ) (f : ℕ → L2 μ) :
    (⇑(∑ n ∈ s, f n)) =ᵐ[μ] (fun z => ∑ n ∈ s, f n z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z hz
    exact hz
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ n ∈ s, f n), ih] with z hz hz'
    change (f a + ∑ n ∈ s, f n) z = f a z + (∑ n ∈ s, f n) z at hz
    rw [hz, hz']

variable {μ : Measure ℂ}

/-- The entire series represents the actual L2 diagonal operator. This proves
the passage between locally uniform convergence and convergence in L2. -/
theorem polynomialSeries_represents
    (b : HilbertBasis ℕ ℂ (L2 μ)) (p : ℕ → Polynomial ℂ)
    (hp : ∀ n, (b n : ℂ → ℂ) =ᵐ[μ] (fun z => (p n).eval z)) (x : L2 μ) :
    (diagonalSmoothing b (smoothingWeight p) x : ℂ → ℂ) =ᵐ[μ]
      polynomialSeries p (fun n => b.repr x n) := by
  let t : ℕ → L2 μ := fun n => (smoothingWeight p n : ℂ) • basisProjection b n x
  let q : ℕ → ℂ → ℂ := fun n z => (smoothingWeight p n : ℂ) * b.repr x n * (p n).eval z
  have ht : ∀ n, (t n : ℂ → ℂ) =ᵐ[μ] q n := by
    intro n
    have he : t n = ((smoothingWeight p n : ℂ) * b.repr x n) • b n := by
      simp [t, basisProjection_apply, HilbertBasis.repr_apply_apply, smul_smul]
    rw [he]
    filter_upwards [Lp.coeFn_smul ((smoothingWeight p n : ℂ) * b.repr x n) (b n), hp n]
      with z hz hzp
    simpa [q, hzp] using hz
  have hsum : HasSum t (diagonalSmoothing b (smoothingWeight p) x) := by
    exact (diagonalSmoothing_hasSum b (smoothingWeight_summable p)).mapL
      (ContinuousLinearMap.apply ℂ (L2 μ) x)
  have he : ∀ N : ℕ, (⇑(∑ n ∈ Finset.range N, t n)) =ᵐ[μ]
      (fun z => ∑ n ∈ Finset.range N, q n z) := by
    intro N
    filter_upwards [l2_coeFn_finset_sum (Finset.range N) t, ae_all_iff.mpr ht] with z hz hzt
    rw [hz]
    exact Finset.sum_congr rfl (fun n _ => hzt n)
  have hm := (tendstoInMeasure_of_tendsto_Lp hsum.tendsto_sum_nat).congr_left he
  obtain ⟨ns,hns,hae⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hae] with z hz
  have hpoint := (polynomialSeries_hasSum p (fun n => b.repr x n) (norm_nonneg x)
    (hilbert_coefficient_bound b x) z).tendsto_sum_nat
  exact tendsto_nhds_unique hz (hpoint.comp hns.tendsto_atTop)

/-- Polynomial-basis smoothing is modulus-rigid for any measure absolutely
continuous with respect to planar Lebesgue measure. -/
theorem polynomialSmoothing_rigid (hμ : μ ≪ volume)
    (b : HilbertBasis ℕ ℂ (L2 μ)) (p : ℕ → Polynomial ℂ)
    (hp : ∀ n, (b n : ℂ → ℂ) =ᵐ[μ] (fun z => (p n).eval z)) :
    ModulusRigid (diagonalSmoothing b (smoothingWeight p)) := by
  intro x y hpos
  let F := polynomialSeries p (fun n => b.repr x n)
  let G := polynomialSeries p (fun n => b.repr y n)
  have hF := polynomialSeries_represents b p hp x
  have hG := polynomialSeries_represents b p hp y
  have he : μ {z | ‖diagonalSmoothing b (smoothingWeight p) x z‖ =
      ‖diagonalSmoothing b (smoothingWeight p) y z‖} ≤ μ {z | ‖F z‖ = ‖G z‖} := by
    apply measure_mono_ae
    filter_upwards [hF,hG] with z hz hz'
    change (‖diagonalSmoothing b (smoothingWeight p) x z‖ =
      ‖diagonalSmoothing b (smoothingWeight p) y z‖) → ‖F z‖ = ‖G z‖
    rw [hz, hz']
    exact id
  have hv : 0 < volume {z | ‖F z‖ = ‖G z‖} := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    exact (ne_of_gt (hpos.trans_le he)) (hμ hzero)
  obtain ⟨ω,hω,hphase⟩ := entire_phase_of_positive_measure
    (polynomialSeries_entire p _ (norm_nonneg x) (hilbert_coefficient_bound b x))
    (polynomialSeries_entire p _ (norm_nonneg y) (hilbert_coefficient_bound b y)) hv
  refine ⟨ω,hω, diagonalSmoothing_injective b (smoothingWeight_summable p)
    (fun n => ne_of_gt (smoothingWeight_pos p n)) ?_⟩
  rw [map_smul]
  apply Lp.ext
  filter_upwards [hF,hG,Lp.coeFn_smul ω (diagonalSmoothing b (smoothingWeight p) x)] with z hz hz' hs
  rw [hs]
  change diagonalSmoothing b (smoothingWeight p) y z =
    ω * diagonalSmoothing b (smoothingWeight p) x z
  rw [hz, hz']
  exact hphase z

/-- The full smoothing construction, with only the polynomial Hilbert basis
left as an input. All analytic, norm, compactness and rigidity claims are proved. -/
theorem exists_rigid_of_polynomial_basis (hμ : μ ≪ volume)
    (b : HilbertBasis ℕ ℂ (L2 μ)) (p : ℕ → Polynomial ℂ)
    (hp : ∀ n, (b n : ℂ → ℂ) =ᵐ[μ] (fun z => (p n).eval z)) :
    ∃ C : L2 μ →L[ℂ] L2 μ, C.IsPositive ∧ ‖C‖ ≤ (1:ℝ)/8 ∧
      IsCompactOperator C ∧ Function.Injective C ∧ ModulusRigid C := by
  refine ⟨diagonalSmoothing b (smoothingWeight p),
    diagonalSmoothing_positive b (smoothingWeight_summable p)
      (fun n => (smoothingWeight_pos p n).le), ?_,
    diagonalSmoothing_compact b (smoothingWeight_summable p),
    diagonalSmoothing_injective b (smoothingWeight_summable p)
      (fun n => ne_of_gt (smoothingWeight_pos p n)),
    polynomialSmoothing_rigid hμ b p hp⟩
  exact (diagonalSmoothing_norm_le b (smoothingWeight_summable p)
    (fun n => (smoothingWeight_pos p n).le)).trans (smoothingWeight_tsum_le p)

end OperatorPhaseRetrieval

end
