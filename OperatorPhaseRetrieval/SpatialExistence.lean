import OperatorPhaseRetrieval.ProbabilitySpatial
import OperatorPhaseRetrieval.WeightedL2

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

/-! Existence of spatial unitaries for atomless sigma-finite standard Borel measures. -/
open MeasureTheory Set
namespace OperatorPhaseRetrieval
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y]

theorem sigmaFinite_spatial_unitary (μ : Measure X) [SigmaFinite μ] [NeZero μ] [NullSingletonClass μ] :
    ∃ W : L2 uniformUnit ≃ₗᵢ[ℂ] L2 μ, ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  obtain ⟨ν,hfin,hμν,hνμ⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  let : IsFiniteMeasure ν := hfin
  have hν0 : ν ≠ 0 := by
    intro h
    have hz : μ univ = 0 := hμν (by simp [h])
    exact (NeZero.ne μ) (Measure.measure_univ_eq_zero.mp hz)
  let : NeZero ν := ⟨hν0⟩
  let ρ : Measure X := (ν univ)⁻¹ • ν
  let : IsProbabilityMeasure ρ := isProbabilityMeasureSMul
  have hμρ : μ ≪ ρ := hμν.trans
    (Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr (measure_ne_top ν univ)))
  have hρμ : ρ ≪ μ := Measure.smul_absolutelyContinuous.trans hνμ
  let : NullSingletonClass ρ := ⟨fun x => hρμ (measure_singleton x)⟩
  obtain ⟨A,hA⟩ := equivalent_measures_unitary (μ := μ) ρ hμρ hρμ
  obtain ⟨B,hB⟩ := probability_spatial_unitary ρ
  refine ⟨B.trans A, fun f g => ?_⟩
  exact (hA (B f) (B g)).trans (hB f g)

/-- Lemma 6.1: existence, including normalization, null sets, and density weights. -/
theorem exists_spatial_unitary (μ : Measure X) (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] [NeZero μ] [NeZero ν] [NullSingletonClass μ] [NullSingletonClass ν] :
    ∃ W : L2 μ ≃ₗᵢ[ℂ] L2 ν, ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  obtain ⟨A,hA⟩ := sigmaFinite_spatial_unitary μ
  obtain ⟨B,hB⟩ := sigmaFinite_spatial_unitary ν
  refine ⟨A.symm.trans B, fun f g => ?_⟩
  have ha : ModEq (A.symm f) (A.symm g) ↔ ModEq f g := by
    simpa using (hA (A.symm f) (A.symm g)).symm
  exact (hB (A.symm f) (A.symm g)).trans ha

end OperatorPhaseRetrieval

end
