import OperatorPhaseRetrieval.BlockRotation

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra

/-! # A compact injective self-adjoint diagonal smoothing operator

The basis is an explicit parameter. Its polynomial realization is a separate
construction; no existence of such a realization is assumed here.
-/

open Set Filter
open scoped Topology ComplexConjugate
namespace OperatorPhaseRetrieval
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def basisProjection (b : HilbertBasis ℕ ℂ H) (n : ℕ) : H →L[ℂ] H :=
  (innerSL ℂ (b n)).smulRight (b n)

omit [CompleteSpace H] in
@[simp] theorem basisProjection_apply (b : HilbertBasis ℕ ℂ H) (n : ℕ) (x : H) :
    basisProjection b n x = inner (𝕜 := ℂ) (b n) x • b n := rfl

omit [CompleteSpace H] in
theorem basisProjection_norm (b : HilbertBasis ℕ ℂ H) (n : ℕ) :
    ‖basisProjection b n‖ = 1 := by
  simp [basisProjection, ContinuousLinearMap.norm_smulRight_apply,
    b.orthonormal.norm_eq_one]

theorem basisProjection_selfAdjoint (b : HilbertBasis ℕ ℂ H) (n : ℕ) :
    IsSelfAdjoint (basisProjection b n) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner (𝕜 := ℂ) (inner (𝕜 := ℂ) (b n) x • b n) y =
    inner (𝕜 := ℂ) x (inner (𝕜 := ℂ) (b n) y • b n)
  simp only [inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

omit [CompleteSpace H] in
theorem basisProjection_basis (b : HilbertBasis ℕ ℂ H) (n m : ℕ) :
    basisProjection b n (b m) = if n = m then b n else 0 := by
  classical
  rw [basisProjection_apply, (orthonormal_iff_ite.mp b.orthonormal) n m]
  split_ifs <;> simp_all

def diagonalSmoothing (b : HilbertBasis ℕ ℂ H) (w : ℕ → ℝ) : H →L[ℂ] H :=
  ∑' n, (w n : ℂ) • basisProjection b n

theorem diagonalSmoothing_summable (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) : Summable (fun n => (w n : ℂ) • basisProjection b n) := by
  apply Summable.of_norm
  simpa [norm_smul, basisProjection_norm] using hw.abs

theorem diagonalSmoothing_hasSum (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) : HasSum (fun n => (w n : ℂ) • basisProjection b n)
      (diagonalSmoothing b w) := (diagonalSmoothing_summable b hw).hasSum

omit [CompleteSpace H] in
theorem diagonalSmoothing_norm_le (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n) :
    ‖diagonalSmoothing b w‖ ≤ ∑' n, w n := by
  have hnrm : Summable (fun n => ‖(w n : ℂ) • basisProjection b n‖) := by
    simpa [norm_smul, basisProjection_norm] using hw.abs
  have h := norm_tsum_le_tsum_norm hnrm
  simpa [diagonalSmoothing, norm_smul, basisProjection_norm, abs_of_nonneg (hn _)] using h

theorem diagonalSmoothing_selfAdjoint (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) : IsSelfAdjoint (diagonalSmoothing b w) := by
  have hs : IsClosed {T : H →L[ℂ] H | IsSelfAdjoint T} :=
    isClosed_eq continuous_star continuous_id
  apply hs.mem_of_tendsto (diagonalSmoothing_hasSum b hw)
  apply Filter.Eventually.of_forall
  intro s
  change IsSelfAdjoint (∑ n ∈ s, (w n : ℂ) • basisProjection b n)
  apply (selfAdjoint (H →L[ℂ] H)).sum_mem
  intro n _
  exact (show IsSelfAdjoint (w n : ℂ) from by simp [IsSelfAdjoint]).smul
    (basisProjection_selfAdjoint b n)

theorem diagonalSmoothing_basis (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) (m : ℕ) : diagonalSmoothing b w (b m) = (w m : ℂ) • b m := by
  classical
  have hs := (diagonalSmoothing_hasSum b hw).mapL
    (ContinuousLinearMap.apply ℂ H (b m))
  have he : (fun n => ((w n : ℂ) • basisProjection b n) (b m)) =
      (fun n => if n = m then (w m : ℂ) • b m else 0) := by
    funext n
    simp only [smul_apply, basisProjection_basis]
    split_ifs <;> simp_all
  change HasSum (fun n => ((w n : ℂ) • basisProjection b n) (b m))
    (diagonalSmoothing b w (b m)) at hs
  rw [he] at hs
  simpa using hs.unique (hasSum_ite_eq m ((w m : ℂ) • b m))

theorem diagonalSmoothing_injective (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) (hne : ∀ n, w n ≠ 0) :
    Function.Injective (diagonalSmoothing b w) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change diagonalSmoothing b w x = 0 at hx
  apply b.repr.injective
  apply lp.ext
  funext n
  rw [HilbertBasis.repr_apply_apply]
  have hs := (diagonalSmoothing_selfAdjoint b hw).isSymmetric (b n) x
  change inner (𝕜 := ℂ) (diagonalSmoothing b w (b n)) x =
    inner (𝕜 := ℂ) (b n) (diagonalSmoothing b w x) at hs
  rw [diagonalSmoothing_basis b hw n, hx, inner_zero_right, inner_smul_left] at hs
  have hn : star (w n : ℂ) ≠ 0 := by simpa using hne n
  simpa using (mul_eq_zero.mp hs).resolve_left hn

omit [CompleteSpace H] in
theorem basisProjection_compact (b : HilbertBasis ℕ ℂ H) (n : ℕ) :
    IsCompactOperator (basisProjection b n) := by
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (basisProjection b n).toLinearMap zero_lt_one).2
  refine ⟨(fun c : ℂ => c • b n) '' Metric.closedBall 0 1,
    (isCompact_closedBall (0 : ℂ) 1).image (continuous_id.smul continuous_const), ?_⟩
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨inner (𝕜 := ℂ) (b n) x, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  exact (norm_inner_le_norm (b n) x).trans (by simpa [b.orthonormal.norm_eq_one] using hx')

theorem diagonalSmoothing_compact (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) : IsCompactOperator (diagonalSmoothing b w) := by
  apply isCompactOperator_of_tendsto (diagonalSmoothing_hasSum b hw)
  apply Filter.Eventually.of_forall
  intro s
  change (∑ n ∈ s, (w n : ℂ) • basisProjection b n) ∈ compactOperator (RingHom.id ℂ) H H
  apply (compactOperator (RingHom.id ℂ) H H).sum_mem
  intro n _
  exact (basisProjection_compact b n).smul (w n : ℂ)

theorem diagonalSmoothing_positive (b : HilbertBasis ℕ ℂ H) {w : ℕ → ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n) :
    (diagonalSmoothing b w).IsPositive := by
  refine ⟨(diagonalSmoothing_selfAdjoint b hw).isSymmetric, ?_⟩
  intro x
  have hs := (diagonalSmoothing_hasSum b hw).mapL (ContinuousLinearMap.apply ℂ H x)
  have ht : Tendsto (fun s : Finset ℕ =>
      (inner (𝕜 := ℂ) (∑ n ∈ s, ((w n : ℂ) • basisProjection b n) x) x).re)
      atTop (𝓝 (inner (𝕜 := ℂ) (diagonalSmoothing b w x) x).re) :=
    (Complex.continuous_re.tendsto _).comp (hs.inner tendsto_const_nhds)
  apply ge_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro s
  simp only [sum_inner, Complex.re_sum]
  apply Finset.sum_nonneg
  intro n _
  change 0 ≤ (inner (𝕜 := ℂ) ((w n : ℂ) • basisProjection b n x) x).re
  rw [basisProjection_apply, inner_smul_left, inner_smul_left]
  simp only [Complex.conj_ofReal, ← mul_assoc]
  have hc : starRingEnd ℂ (inner (𝕜 := ℂ) (b n) x) * inner (𝕜 := ℂ) (b n) x =
      (Complex.normSq (inner (𝕜 := ℂ) (b n) x) : ℂ) := Complex.normSq_eq_conj_mul_self.symm
  rw [mul_assoc, hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (hn n) (Complex.normSq_nonneg _)

end OperatorPhaseRetrieval

end
