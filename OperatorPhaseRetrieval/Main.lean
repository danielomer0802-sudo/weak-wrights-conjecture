import OperatorPhaseRetrieval.SpatialTransfer
import OperatorPhaseRetrieval.Corollaries
import OperatorPhaseRetrieval.NearIdentity
import OperatorPhaseRetrieval.RigidModel
import OperatorPhaseRetrieval.SpatialExistence
import OperatorPhaseRetrieval.DoubleL2
import OperatorPhaseRetrieval.StandardBorelDouble

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

/-! Unconditional main theorem and corollaries of the paper. -/
open MeasureTheory
namespace OperatorPhaseRetrieval

/-- A spatial realization of the two-copy model on any atomless standard space. -/
theorem exists_double_spatial_unitary {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [NeZero μ] [NullSingletonClass μ]
    [SigmaFinite ν] [NeZero ν] [NullSingletonClass ν] :
    ∃ W : L2 ν ≃ₗᵢ[ℂ] SumL2 (L2 μ), ∀ f g, PairModEq (W f) (W g) ↔ ModEq f g := by
  let : IsFiniteMeasure (doubleMeasure μ) := doubleMeasure_finite μ
  let : NeZero (doubleMeasure μ) := ⟨doubleMeasure_ne_zero μ⟩
  let : NullSingletonClass (doubleMeasure μ) := doubleMeasure_noAtoms μ
  let : StandardBorelSpace (X ⊕ X) := standardBorel_double
  obtain ⟨V,hV⟩ := exists_spatial_unitary ν (doubleMeasure μ)
  let W : L2 ν ≃ₗᵢ[ℂ] SumL2 (L2 μ) := V.trans (doubleL2Equiv μ).symm
  refine ⟨W, fun f g => ?_⟩
  have hd := doubleL2Equiv_modEq μ (W f) (W g)
  have he : ModEq (V f) (V g) ↔ PairModEq (W f) (W g) := by
    simpa only [W, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply] using hd
  exact he.symm.trans (hV f g)

/-- Theorem 2.1, with no analytic-model or spatial-isomorphism hypotheses. -/
theorem main : MainStatement := by
  obtain ⟨μ,hfin,hμ0,hμv,C,hC,hsmall,hcompact,hinj,hrigid⟩ := exists_rigid_model
  let : IsFiniteMeasure μ := hfin
  let : NeZero μ := ⟨hμ0⟩
  let : NullSingletonClass μ := ⟨fun z => hμv (measure_singleton z)⟩
  obtain ⟨W,hW⟩ := exists_double_spatial_unitary μ (volume : Measure ℝ)
  exact main_of_rigid_spatial_model C hC.isSelfAdjoint hsmall hrigid W hW

/-- Corollary 2.2: a unitary of order three gives phase retrieval with I,U,U². -/
theorem exists_order_three_phase_retrieval :
    ∃ U : RealL2 →L[ℂ] RealL2, IsUnitary U ∧ U^3=1 ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ModEq ((U^2) f) ((U^2) g) →
        PhaseRelated f g := by
  obtain ⟨P,hP,hretr⟩ := main
  exact order_three_of_projection ModEq P hP (fun η hη hi => (hretr η hη hi).2)

/-- Corollary 2.2: both nontrivial measurements can be arbitrarily near the identity. -/
theorem exists_near_identity_phase_retrieval (ε : ℝ) (hε : 0 < ε) :
    ∃ U : RealL2 →L[ℂ] RealL2, IsUnitary U ∧ ‖U-1‖<ε ∧ ‖U^2-1‖<ε ∧
      ∀ f g, ModEq f g → ModEq (U f) (U g) → ModEq ((U^2) f) ((U^2) g) →
        PhaseRelated f g := by
  obtain ⟨P,hP,hretr⟩ := main
  exact near_identity_of_projection ModEq P hP (fun η hη hi => (hretr η hη hi).2) ε hε

/-- Corollary 6.2 on every nonzero atomless sigma-finite standard Borel measure space. -/
theorem phase_retrieval_on_standardBorel {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [SigmaFinite μ] [NeZero μ] [NullSingletonClass μ] :
    ProjectionWorks (@ModEq X _ μ) := by
  obtain ⟨W,hW⟩ := exists_spatial_unitary μ (volume : Measure ℝ)
  exact transfer_projectionWorks W hW main

end OperatorPhaseRetrieval

end
