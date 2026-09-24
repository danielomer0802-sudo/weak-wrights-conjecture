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
open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory Set
open Set
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-! Measurable equivalences and standard Borel structure of a two-copy space. -/
open MeasureTheory
namespace OperatorPhaseRetrieval

theorem standardBorel_of_measurableEquiv {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    (e : X ≃ᵐ Y) : StandardBorelSpace X := by
  let := upgradeStandardBorel Y
  let : TopologicalSpace X := TopologicalSpace.induced e inferInstance
  let : PolishSpace X := e.toEquiv.polishSpace_induced
  let : BorelSpace X := e.measurableEmbedding.borelSpace ⟨rfl⟩
  infer_instance

def doubleMeasurableEquiv {X : Type*} [MeasurableSpace X] : (X ⊕ X) ≃ᵐ (Bool × X) where
  toFun := Sum.elim (fun x => (false,x)) (fun x => (true,x))
  invFun p := if p.1 = true then Sum.inr p.2 else Sum.inl p.2
  left_inv x := by cases x <;> rfl
  right_inv p := by rcases p with ⟨b,x⟩; cases b <;> rfl
  measurable_toFun := (measurable_const.prodMk measurable_id).sumElim
    (measurable_const.prodMk measurable_id)
  measurable_invFun := Measurable.ite (measurable_fst (measurableSet_singleton true))
    (measurable_inr.comp measurable_snd) (measurable_inl.comp measurable_snd)

theorem standardBorel_double {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] :
    StandardBorelSpace (X ⊕ X) := standardBorel_of_measurableEquiv doubleMeasurableEquiv

end OperatorPhaseRetrieval

end
