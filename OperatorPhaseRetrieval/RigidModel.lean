import OperatorPhaseRetrieval.PolynomialBasis
import OperatorPhaseRetrieval.ProductApproximation

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
open Set

/-! Unconditional construction of the polynomial-dense measure and rigid operator. -/
open MeasureTheory Set
namespace OperatorPhaseRetrieval

theorem uniform_approximation_of_closure_eq_top (K : Set ℂ) [CompactSpace K]
    (hK : uniformPolynomialClosure K = ⊤) (f : C(K,ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z : K, ‖p.eval (z:ℂ) - f z‖ < ε := by
  have hf : f ∈ closure ((uniformPolynomial K).range : Set C(K,ℂ)) := by
    change f ∈ uniformPolynomialClosure K
    rw [hK]
    trivial
  obtain ⟨g,⟨p,hp⟩,hg⟩ := Metric.mem_closure_iff.mp hf ε hε
  change uniformPolynomial K p = g at hp
  refine ⟨p, fun z => ?_⟩
  rw [← uniformPolynomial_apply, hp, ← dist_eq_norm, dist_comm]
  exact (ContinuousMap.dist_apply_le_dist z).trans_lt hg

theorem polynomialL2_dense_of_uniform {K : Set ℂ} (hc : IsCompact K)
    (hK : letI : CompactSpace K := isCompact_iff_compactSpace.mp hc
      uniformPolynomialClosure K = ⊤) :
    (polynomialL2 (polynomials_memLp_compact hc)).range.topologicalClosure = ⊤ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let μ := volume.restrict K
  let : IsFiniteMeasure μ := ⟨by simpa [μ] using hc.measure_lt_top⟩
  let : μ.WeaklyRegular := Measure.WeaklyRegular.restrict_of_measure_ne_top hc.measure_lt_top.ne
  let T := polynomialL2 (polynomials_memLp_compact hc)
  let B : ℝ := (measureUnivNNReal μ : ℝ) ^ (2:ENNReal).toReal⁻¹
  have hB : 0 ≤ B := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hi : range (BoundedContinuousFunction.toLp 2 μ ℂ : (BoundedContinuousFunction ℂ ℂ) →L[ℂ] L2 μ) ⊆
      ((LinearMap.range T).topologicalClosure : Set (L2 μ)) := by
    rintro _ ⟨g,rfl⟩
    change BoundedContinuousFunction.toLp 2 μ ℂ g ∈ closure ((LinearMap.range T) : Set (L2 μ))
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let δ := ε/(B+1)
    have hδ : 0 < δ := div_pos hε (by linarith)
    let gc : C(K,ℂ) := ⟨fun z => g z, g.continuous.comp continuous_subtype_val⟩
    obtain ⟨p,hp⟩ := uniform_approximation_of_closure_eq_top K hK gc hδ
    refine ⟨T p, ⟨p,rfl⟩, ?_⟩
    have hb : ‖T p - BoundedContinuousFunction.toLp 2 μ ℂ g‖ ≤ B*δ := by
      apply Lp.norm_le_of_ae_bound hδ.le
      filter_upwards [Lp.coeFn_sub (T p) (BoundedContinuousFunction.toLp 2 μ ℂ g),
        polynomialL2_coeFn (polynomials_memLp_compact hc) p,
        BoundedContinuousFunction.coeFn_toLp 2 μ ℂ g,
        ae_restrict_mem hc.measurableSet] with z hz ht hg hzK
      rw [hz]
      change ‖(polynomialL2 (polynomials_memLp_compact hc) p) z -
        (BoundedContinuousFunction.toLp 2 μ ℂ g) z‖ ≤ δ
      rw [ht,hg]
      exact (hp ⟨z,hzK⟩).le
    rw [dist_comm, dist_eq_norm]
    apply hb.trans_lt
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by linarith : 0 < B+1)]
    nlinarith
  have hd := BoundedContinuousFunction.toLp_denseRange (p := 2) ℂ μ ℂ (by norm_num)
  apply top_unique
  intro f _
  exact closure_minimal hi (LinearMap.range T).isClosed_topologicalClosure (hd f)

/-- The approximation input of Proposition 4.1 now has an actual witness. -/
theorem exists_polynomial_dense_measure :
    ∃ μ : Measure ℂ, IsFiniteMeasure μ ∧ μ ≠ 0 ∧ μ ≪ volume ∧
      ∃ hm : ∀ p : Polynomial ℂ, MemLp (fun z => p.eval z) 2 μ,
        (polynomialL2 hm).range.topologicalClosure = ⊤ := by
  obtain ⟨F,hFc,hFI,hFq,hFv⟩ := exists_irrational_compact
  let K := planarProduct F
  have hc : IsCompact K := planarProduct_compact hFc
  have hv : 0 < volume K := by
    rw [planarProduct_volume hFc.measurableSet]
    exact ENNReal.mul_pos hFv.ne' hFv.ne'
  have hne : F.Nonempty := nonempty_of_measure_ne_zero hFv.ne'
  refine ⟨volume.restrict K, ⟨by simpa using hc.measure_lt_top⟩, ?_, Measure.absolutelyContinuous_of_le Measure.restrict_le_self,
    polynomials_memLp_compact hc, ?_⟩
  · exact fun h => hv.ne' (Measure.restrict_eq_zero.mp h)
  · exact polynomialL2_dense_of_uniform hc (planarProduct_polynomialClosure hFc hne hFq)

/-- Proposition 4.1, including existence of the measure and all approximation data. -/
theorem exists_rigid_model :
    ∃ μ : Measure ℂ, IsFiniteMeasure μ ∧ μ ≠ 0 ∧ μ ≪ volume ∧
      ∃ C : L2 μ →L[ℂ] L2 μ, C.IsPositive ∧ ‖C‖ ≤ (1:ℝ)/8 ∧
        IsCompactOperator C ∧ Function.Injective C ∧ ModulusRigid C := by
  obtain ⟨μ,hfin,hμ0,hμ,hm,hd⟩ := exists_polynomial_dense_measure
  let : NeZero μ := ⟨hμ0⟩
  exact ⟨μ,hfin,hμ0,hμ,exists_rigid_of_polynomial_density hμ hm hd⟩

end OperatorPhaseRetrieval

end
