import OperatorPhaseRetrieval.RigidModel

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
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-! Existence and uniqueness of every entire representative in Proposition 4.1. -/
open MeasureTheory Set
namespace OperatorPhaseRetrieval

theorem entire_eq_of_ae_eq {μ : Measure ℂ} [NeZero μ] (hμ : μ ≪ volume)
    {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (he : F =ᵐ[μ] G) : F = G := by
  have hpos : 0 < volume {z | ‖F z-G z‖ = ‖(0:ℂ)‖} := by
    by_contra h
    have hz : μ {z | ‖F z-G z‖ = ‖(0:ℂ)‖} = 0 :=
      hμ (le_antisymm (not_lt.mp h) bot_le)
    have hn : ∀ᵐ z ∂μ, ¬ ‖F z-G z‖ = ‖(0:ℂ)‖ := ae_iff.mpr (by simpa using hz)
    have hf : ∀ᵐ z ∂μ, False := by
      filter_upwards [he,hn] with z he hn
      exact hn (by simp [he])
    exact (Filter.Eventually.exists hf).choose_spec
  have ha := entire_norm_eq_of_positive_measure (hF.sub hG) analyticOnNhd_const hpos
  funext z
  exact sub_eq_zero.mp (norm_eq_zero.mp (by simpa using ha z))

theorem polynomialSmoothing_unique_entire {μ : Measure ℂ} [NeZero μ] (hμ : μ ≪ volume)
    (b : HilbertBasis ℕ ℂ (L2 μ)) (p : ℕ → Polynomial ℂ)
    (hp : ∀ n, (b n : ℂ → ℂ) =ᵐ[μ] (fun z => (p n).eval z)) (f : L2 μ) :
    ∃! F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧
      (diagonalSmoothing b (smoothingWeight p) f : ℂ → ℂ) =ᵐ[μ] F := by
  let F := polynomialSeries p (fun n => b.repr f n)
  have hF : AnalyticOnNhd ℂ F univ :=
    polynomialSeries_entire p _ (norm_nonneg f) (hilbert_coefficient_bound b f)
  have hr : (diagonalSmoothing b (smoothingWeight p) f : ℂ → ℂ) =ᵐ[μ] F :=
    polynomialSeries_represents b p hp f
  exact ⟨F,⟨hF,hr⟩,fun G hG => entire_eq_of_ae_eq hμ hG.1 hF (hG.2.symm.trans hr)⟩

/-- All assertions of Proposition 4.1 for an actual measure and operator. -/
theorem exists_entire_rigid_model :
    ∃ μ : Measure ℂ, IsFiniteMeasure μ ∧ μ ≠ 0 ∧ μ ≪ volume ∧
      ∃ C : L2 μ →L[ℂ] L2 μ, C.IsPositive ∧ IsSelfAdjoint C ∧ ‖C‖ ≤ (1:ℝ)/8 ∧
        IsCompactOperator C ∧ Function.Injective C ∧ ModulusRigid C ∧
        (∀ f : L2 μ, ∃! F : ℂ → ℂ, AnalyticOnNhd ℂ F univ ∧ (C f : ℂ → ℂ) =ᵐ[μ] F) ∧
        (∀ f : L2 μ, f ≠ 0 → ∀ᵐ z ∂μ, C f z ≠ 0) := by
  obtain ⟨μ,hfin,hμ0,hμ,hm,hd⟩ := exists_polynomial_dense_measure
  let : NeZero μ := ⟨hμ0⟩
  obtain ⟨b,p,hp⟩ := polynomial_hilbertBasis_of_dense hμ hm hd
  have hw := smoothingWeight_summable p
  have hr := polynomialSmoothing_rigid hμ b p hp
  refine ⟨μ,hfin,hμ0,hμ,diagonalSmoothing b (smoothingWeight p),
    diagonalSmoothing_positive b hw (fun n => (smoothingWeight_pos p n).le),
    diagonalSmoothing_selfAdjoint b hw,?_,diagonalSmoothing_compact b hw,
    diagonalSmoothing_injective b hw (fun n => ne_of_gt (smoothingWeight_pos p n)),hr,
    polynomialSmoothing_unique_entire hμ b p hp,fun f hf => rigid_nonzero_ae hr hf⟩
  exact (diagonalSmoothing_norm_le b hw (fun n => (smoothingWeight_pos p n).le)).trans
    (smoothingWeight_tsum_le p)

end OperatorPhaseRetrieval

end
