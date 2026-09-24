import OperatorPhaseRetrieval.MathlibImports

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped Topology

/-! Atomless real probability measures have an almost-everywhere inverse CDF. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace OperatorPhaseRetrieval
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]

theorem continuous_atomless_cdf : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [(cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim, (cdf μ).rightLim_eq]
  have hz := (cdf μ).measure_singleton x
  rw [measure_cdf, measure_singleton] at hz
  have hl : cdf μ x ≤ Function.leftLim (cdf μ) x := by
    have := ENNReal.ofReal_eq_zero.mp hz.symm
    linarith
  exact le_antisymm ((cdf μ).mono.leftLim_le le_rfl) hl

theorem cdf_surjective_unitInterval (t : Ioo (0:ℝ) 1) :
    ∃ x : ℝ, cdf μ x = t := by
  obtain ⟨a,ha⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds t.property.1)).exists
  obtain ⟨b,hb⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds t.property.2)).exists
  have hab : a ≤ b := by
    by_contra! hn
    have := (cdf μ).mono hn.le
    linarith
  obtain ⟨x,hx,he⟩ := intermediate_value_Icc hab (continuous_atomless_cdf μ).continuousOn
    ⟨ha.le,hb.le⟩
  exact ⟨x,he⟩

/-- A chosen right inverse is automatically strictly increasing on (0,1). -/
def cdfQuantile (t : Ioo (0:ℝ) 1) : ℝ := (cdf_surjective_unitInterval μ t).choose

theorem cdfQuantile_spec (t : Ioo (0:ℝ) 1) : cdf μ (cdfQuantile μ t) = t :=
  (cdf_surjective_unitInterval μ t).choose_spec

theorem cdfQuantile_strictMono : StrictMono (cdfQuantile μ) := by
  intro s t hst
  by_contra! hn
  have hm := (cdf μ).mono hn
  rw [cdfQuantile_spec, cdfQuantile_spec] at hm
  exact (not_le_of_gt hst) hm

def extendedQuantile (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0:ℝ) 1 then cdfQuantile μ ⟨t,ht⟩ else 0

theorem measurable_extendedQuantile : Measurable (extendedQuantile μ) := by
  apply Measurable.dite (cdfQuantile_strictMono μ).monotone.measurable
    measurable_const measurableSet_Ioo

theorem cdf_extendedQuantile {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    cdf μ (extendedQuantile μ t) = t := by
  rw [extendedQuantile, dif_pos ht, cdfQuantile_spec]

def uniformUnit : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1)

theorem uniformUnit_probability : IsProbabilityMeasure uniformUnit := by
  constructor
  simp [uniformUnit]

theorem quantile_lower {t x : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (h : t < cdf μ x) :
    extendedQuantile μ t < x := by
  by_contra! hn
  have hm := (cdf μ).mono hn
  rw [cdf_extendedQuantile μ ht] at hm
  linarith

theorem quantile_upper {t x : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    (h : extendedQuantile μ t ≤ x) : t ≤ cdf μ x := by
  have hm := (cdf μ).mono h
  rwa [cdf_extendedQuantile μ ht] at hm

theorem quantile_map_uniform : Measure.map (extendedQuantile μ) uniformUnit = μ := by
  let : IsProbabilityMeasure uniformUnit := uniformUnit_probability
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (measurable_extendedQuantile μ) measurableSet_Iic,
    uniformUnit, Measure.restrict_apply ((measurable_extendedQuantile μ) measurableSet_Iic)]
  have hl : Ioo 0 (cdf μ x) ⊆ extendedQuantile μ ⁻¹' Iic x ∩ Ioo 0 1 := by
    intro t ht
    have ht' : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1, ht.2.trans_le (cdf_le_one μ x)⟩
    exact ⟨(quantile_lower μ ht' ht.2).le, ht'⟩
  have hu : extendedQuantile μ ⁻¹' Iic x ∩ Ioo 0 1 ⊆ Ioc 0 (cdf μ x) := by
    intro t ht
    exact ⟨ht.2.1, quantile_upper μ ht.2 ht.1⟩
  apply le_antisymm
  · exact (measure_mono hu).trans_eq (by simpa using ofReal_cdf μ x)
  · exact (by simpa using (ofReal_cdf μ x).symm : μ (Iic x) = volume (Ioo 0 (cdf μ x))).le.trans
      (measure_mono hl)

theorem quantile_measurePreserving : MeasurePreserving (extendedQuantile μ) uniformUnit μ :=
  ⟨measurable_extendedQuantile μ, quantile_map_uniform μ⟩

theorem cdf_quantile_ae : (fun t => cdf μ (extendedQuantile μ t)) =ᵐ[uniformUnit] id := by
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with t ht
  exact cdf_extendedQuantile μ ht

theorem cdf_measurePreserving : MeasurePreserving (cdf μ) μ uniformUnit := by
  refine ⟨(continuous_atomless_cdf μ).measurable, ?_⟩
  calc
    Measure.map (cdf μ) μ = Measure.map (cdf μ) (Measure.map (extendedQuantile μ) uniformUnit) :=
      congrArg (Measure.map (cdf μ)) (quantile_map_uniform μ).symm
    _ = uniformUnit := by
      rw [Measure.map_map (continuous_atomless_cdf μ).measurable (measurable_extendedQuantile μ)]
      change Measure.map (fun t => cdf μ (extendedQuantile μ t)) uniformUnit = uniformUnit
      rw [Measure.map_congr (cdf_quantile_ae μ), Measure.map_id]

theorem quantile_cdf_ae : (fun x => extendedQuantile μ (cdf μ x)) =ᵐ[μ] id := by
  have he : (fun x => extendedQuantile μ (cdf μ x)) =ᵐ[Measure.map (extendedQuantile μ) uniformUnit] id := by
    apply (ae_map_iff (measurable_extendedQuantile μ).aemeasurable
      (measurableSet_eq_fun ((measurable_extendedQuantile μ).comp
        (continuous_atomless_cdf μ).measurable) measurable_id)).mpr
    filter_upwards [cdf_quantile_ae μ] with t ht
    change extendedQuantile μ (cdf μ (extendedQuantile μ t)) = extendedQuantile μ t
    rw [ht]
    rfl
  simpa only [quantile_map_uniform μ] using he

end OperatorPhaseRetrieval

end
