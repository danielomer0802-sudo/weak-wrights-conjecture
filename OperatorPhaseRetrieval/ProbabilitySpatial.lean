import OperatorPhaseRetrieval.AESpatialPullback
import OperatorPhaseRetrieval.AtomlessCDF

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

/-! Spatial L2 classification of atomless standard Borel probability spaces. -/
open MeasureTheory ProbabilityTheory Set
namespace OperatorPhaseRetrieval
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

include μ in
omit [StandardBorelSpace X] in
theorem atomless_probability_uncountable : ¬ Countable X := by
  intro h
  let := h
  have hz := (Set.to_countable (univ : Set X)).measure_zero μ
  simp at hz

theorem exists_probability_coordinates :
    ∃ (a : X → ℝ) (b : ℝ → X),
      MeasurePreserving a μ uniformUnit ∧ MeasurePreserving b uniformUnit μ ∧
      (fun x => b (a x)) =ᵐ[μ] id ∧ (fun t => a (b t)) =ᵐ[uniformUnit] id := by
  let e : X ≃ᵐ ℝ := PolishSpace.measurableEquivOfNotCountable
    (atomless_probability_uncountable μ) (by exact not_countable)
  let ν := Measure.map e μ
  have he : MeasurePreserving e μ ν := ⟨e.measurable, rfl⟩
  let : IsProbabilityMeasure ν := by exact Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  let : NullSingletonClass ν := ⟨fun r => by
    rw [show ν = Measure.map e μ from rfl, Measure.map_apply e.measurable (measurableSet_singleton r)]
    have hp : e ⁻¹' {r} = {e.symm r} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      exact e.eq_symm_apply.symm
    rw [hp, measure_singleton]⟩
  refine ⟨(cdf ν) ∘ e, e.symm ∘ extendedQuantile ν,
    (cdf_measurePreserving ν).comp he, (he.symm e).comp (quantile_measurePreserving ν), ?_, ?_⟩
  · filter_upwards [he.quasiMeasurePreserving.ae (quantile_cdf_ae ν)] with x hx
    change e.symm (extendedQuantile ν (cdf ν (e x))) = x
    rw [hx]
    exact e.symm_apply_apply x
  · filter_upwards [cdf_quantile_ae ν] with t ht
    simpa only [Function.comp_apply, e.apply_symm_apply] using ht

theorem probability_spatial_unitary :
    ∃ W : L2 uniformUnit ≃ₗᵢ[ℂ] L2 μ, ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  obtain ⟨a,b,ha,hb,hba,hab⟩ := exists_probability_coordinates μ
  exact ⟨aeSpatialPullback a b ha hb hba hab, aeSpatialPullback_modEq a b ha hb hba hab⟩

end OperatorPhaseRetrieval

end
