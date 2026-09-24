import OperatorPhaseRetrieval.Main

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

/-! Completion of a measure does not change its L2 phase-retrieval problem. -/
open MeasureTheory
namespace OperatorPhaseRetrieval
variable {X : Type*} [mX : MeasurableSpace X] (μ : Measure X)

theorem completion_identity_preserving :
    @MeasurePreserving (NullMeasurableSpace X μ) X
      (NullMeasurableSpace.instMeasurableSpace (μ := μ)) mX
      (fun x => x) μ.completion μ := by
  have hm : @Measurable (NullMeasurableSpace X μ) X
      (NullMeasurableSpace.instMeasurableSpace (μ := μ)) mX (fun x => x) :=
    fun s hs => hs.nullMeasurableSet
  refine ⟨hm,?_⟩
  ext s hs
  rw [Measure.map_apply hm hs]
  rfl

theorem completion_pullback_surjective : Function.Surjective
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x : NullMeasurableSpace X μ => (x : X))
      (completion_identity_preserving μ) : L2 μ →ₗᵢ[ℂ] L2 μ.completion) := by
  intro f
  have hnull : NullMeasurable (fun x : X => f x) μ := (Lp.stronglyMeasurable f).measurable
  have ha := hnull.aemeasurable
  let g : X → ℂ := ha.mk (fun x => f x)
  have hg : Measurable g := ha.measurable_mk
  have he : (fun x : X => f x) =ᵐ[μ] g := ha.ae_eq_mk
  have hgc : MemLp (fun x : NullMeasurableSpace X μ => g x) 2 μ.completion :=
    MemLp.ae_eq he (Lp.memLp f)
  have hgm : AEStronglyMeasurable g
      (Measure.map (fun x : NullMeasurableSpace X μ => (x : X)) μ.completion) := by
    rw [(completion_identity_preserving μ).map_eq]
    exact hg.aestronglyMeasurable
  have hglp : MemLp g 2 μ := by
    rw [← (completion_identity_preserving μ).map_eq]
    exact (memLp_map_measure_iff hgm (completion_identity_preserving μ).aemeasurable).mpr hgc
  refine ⟨hglp.toLp g,?_⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (hglp.toLp g)
    (completion_identity_preserving μ),hglp.coeFn_toLp,he] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

def completionL2Equiv : L2 μ ≃ₗᵢ[ℂ] L2 μ.completion :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ (fun x : NullMeasurableSpace X μ => (x : X))
      (completion_identity_preserving μ)) (completion_pullback_surjective μ)

theorem completionL2Equiv_coeFn (f : L2 μ) :
    (completionL2Equiv μ f : NullMeasurableSpace X μ → ℂ) =ᵐ[μ.completion]
      (fun x => f x) := Lp.coeFn_compMeasurePreserving f (completion_identity_preserving μ)

theorem completionL2Equiv_modEq (f g : L2 μ) :
    ModEq (completionL2Equiv μ f) (completionL2Equiv μ g) ↔ ModEq f g := by
  have hf := completionL2Equiv_coeFn μ f
  have hg := completionL2Equiv_coeFn μ g
  constructor
  · intro h
    filter_upwards [h,hf,hg] with x hx hy hz
    exact Eq.trans (Eq.symm (congrArg norm hy)) (Eq.trans hx (congrArg norm hz))
  · intro h
    filter_upwards [h,hf,hg] with x hx hy hz
    exact Eq.trans (congrArg norm hy) (Eq.trans hx (Eq.symm (congrArg norm hz)))

/-- Lemma 6.1 also holds between completed standard Borel measure spaces. -/
theorem exists_spatial_unitary_completions {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace X] [StandardBorelSpace Y] (ν : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] [NeZero μ] [NeZero ν] [NullSingletonClass μ] [NullSingletonClass ν] :
    ∃ W : L2 μ.completion ≃ₗᵢ[ℂ] L2 ν.completion,
      ∀ f g, ModEq (W f) (W g) ↔ ModEq f g := by
  obtain ⟨A,hA⟩ := exists_spatial_unitary μ ν
  let B := completionL2Equiv μ
  let C := completionL2Equiv ν
  refine ⟨(B.symm.trans A).trans C,fun f g => ?_⟩
  have hB : ModEq (B.symm f) (B.symm g) ↔ ModEq f g := by
    simpa only [B,LinearIsometryEquiv.apply_symm_apply] using
      (completionL2Equiv_modEq μ (B.symm f) (B.symm g)).symm
  exact (completionL2Equiv_modEq ν _ _).trans ((hA _ _).trans hB)

/-- Corollary 6.2, including the completed measure space. -/
theorem phase_retrieval_on_completion [StandardBorelSpace X]
    [SigmaFinite μ] [NeZero μ] [NullSingletonClass μ] :
    ProjectionWorks (@ModEq (NullMeasurableSpace X μ) _ μ.completion) := by
  apply transfer_projectionWorks (completionL2Equiv μ).symm
    (hS := phase_retrieval_on_standardBorel μ)
  intro f g
  simpa using (completionL2Equiv_modEq μ ((completionL2Equiv μ).symm f)
    ((completionL2Equiv μ).symm g)).symm

end OperatorPhaseRetrieval

end
