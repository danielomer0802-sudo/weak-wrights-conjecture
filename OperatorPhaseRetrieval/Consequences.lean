import OperatorPhaseRetrieval.Completion

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

/-! The two unitary corollaries on standard Borel spaces and their completions. -/
open MeasureTheory
namespace OperatorPhaseRetrieval
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  (μ : Measure X) [SigmaFinite μ] [NeZero μ] [NullSingletonClass μ]

theorem order_three_on_standardBorel :
    ∃ U : L2 μ →L[ℂ] L2 μ, IsUnitary U ∧ U^3=1 ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ModEq ((U^2) f) ((U^2) g) →
        PhaseRelated f g := by
  obtain ⟨P,hP,hr⟩ := phase_retrieval_on_standardBorel μ
  exact order_three_of_projection ModEq P hP (fun η hη hi => (hr η hη hi).2)

theorem near_identity_on_standardBorel (ε : ℝ) (hε : 0 < ε) :
    ∃ U : L2 μ →L[ℂ] L2 μ, IsUnitary U ∧ ‖U-1‖<ε ∧ ‖U^2-1‖<ε ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ModEq ((U^2) f) ((U^2) g) →
        PhaseRelated f g := by
  obtain ⟨P,hP,hr⟩ := phase_retrieval_on_standardBorel μ
  exact near_identity_of_projection ModEq P hP (fun η hη hi => (hr η hη hi).2) ε hε

theorem order_three_on_completion :
    ∃ U : L2 μ.completion →L[ℂ] L2 μ.completion, IsUnitary U ∧ U^3=1 ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ModEq ((U^2) f) ((U^2) g) →
        PhaseRelated f g := by
  obtain ⟨P,hP,hr⟩ := phase_retrieval_on_completion μ
  exact order_three_of_projection ModEq P hP (fun η hη hi => (hr η hη hi).2)

theorem near_identity_on_completion (ε : ℝ) (hε : 0 < ε) :
    ∃ U : L2 μ.completion →L[ℂ] L2 μ.completion, IsUnitary U ∧ ‖U-1‖<ε ∧ ‖U^2-1‖<ε ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ModEq ((U^2) f) ((U^2) g) →
        PhaseRelated f g := by
  obtain ⟨P,hP,hr⟩ := phase_retrieval_on_completion μ
  exact near_identity_of_projection ModEq P hP (fun η hη hi => (hr η hη hi).2) ε hε

end OperatorPhaseRetrieval

end
