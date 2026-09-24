import OperatorPhaseRetrieval.AmplificationTheorem
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

/-! The Hilbert direct sum is L2 of the disjoint union, with its actual modulus. -/
open MeasureTheory Set
namespace OperatorPhaseRetrieval
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def doubleMeasure : Measure (X ⊕ X) := Measure.map Sum.inl μ + Measure.map Sum.inr μ

theorem inl_measurableEmbedding : MeasurableEmbedding (@Sum.inl X X) :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩

theorem inr_measurableEmbedding : MeasurableEmbedding (@Sum.inr X X) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩

theorem double_ae_iff {P : X ⊕ X → Prop} :
    (∀ᵐ s ∂doubleMeasure μ, P s) ↔ (∀ᵐ x ∂μ, P (Sum.inl x)) ∧ ∀ᵐ x ∂μ, P (Sum.inr x) := by
  rw [doubleMeasure, ae_add_measure_iff]
  simp only [ae_iff, inl_measurableEmbedding.map_apply, inr_measurableEmbedding.map_apply]
  rfl

def doubleFunction (x : SumL2 (L2 μ)) : X ⊕ X → ℂ := Sum.elim x.fst x.snd

theorem doubleFunction_memLp (x : SumL2 (L2 μ)) : MemLp (doubleFunction μ x) 2 (doubleMeasure μ) := by
  have hl : MemLp (doubleFunction μ x) 2 (Measure.map Sum.inl μ) :=
    inl_measurableEmbedding.memLp_map_measure_iff.mpr (Lp.memLp x.fst)
  have hr : MemLp (doubleFunction μ x) 2 (Measure.map Sum.inr μ) :=
    inr_measurableEmbedding.memLp_map_measure_iff.mpr (Lp.memLp x.snd)
  apply (memLp_two_iff_integrable_sq_norm
    (hl.aestronglyMeasurable.add_measure hr.aestronglyMeasurable)).mpr
  exact ((memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mp hl).add_measure
    ((memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mp hr)

theorem doubleFunction_add (x y : SumL2 (L2 μ)) :
    doubleFunction μ (x+y) =ᵐ[doubleMeasure μ] doubleFunction μ x + doubleFunction μ y := by
  apply (double_ae_iff μ).mpr
  exact ⟨Lp.coeFn_add x.fst y.fst, Lp.coeFn_add x.snd y.snd⟩

theorem doubleFunction_smul (c : ℂ) (x : SumL2 (L2 μ)) :
    doubleFunction μ (c • x) =ᵐ[doubleMeasure μ] c • doubleFunction μ x := by
  apply (double_ae_iff μ).mpr
  exact ⟨Lp.coeFn_smul c x.fst, Lp.coeFn_smul c x.snd⟩

def doubleL2Map : SumL2 (L2 μ) →ₗ[ℂ] L2 (doubleMeasure μ) where
  toFun x := (doubleFunction_memLp μ x).toLp _
  map_add' x y := by
    apply Lp.ext
    filter_upwards [(doubleFunction_memLp μ (x+y)).coeFn_toLp,
      (doubleFunction_memLp μ x).coeFn_toLp,(doubleFunction_memLp μ y).coeFn_toLp,
      Lp.coeFn_add ((doubleFunction_memLp μ x).toLp _) ((doubleFunction_memLp μ y).toLp _),
      doubleFunction_add μ x y] with s hxy hx hy hadd hfun
    simp only [Pi.add_apply] at hadd hfun
    rw [hxy,hadd,hx,hy,hfun]
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [(doubleFunction_memLp μ (c • x)).coeFn_toLp,
      (doubleFunction_memLp μ x).coeFn_toLp,
      Lp.coeFn_smul c ((doubleFunction_memLp μ x).toLp _),doubleFunction_smul μ c x]
      with s hcx hx hsmul hfun
    simp only [Pi.smul_apply] at hsmul hfun
    simp only [RingHom.id_apply]
    rw [hcx,hsmul,hx,hfun]

theorem doubleL2Map_coeFn (x : SumL2 (L2 μ)) :
    (doubleL2Map μ x : X ⊕ X → ℂ) =ᵐ[doubleMeasure μ] doubleFunction μ x :=
  (doubleFunction_memLp μ x).coeFn_toLp

theorem doubleL2Map_norm (x : SumL2 (L2 μ)) : ‖doubleL2Map μ x‖ = ‖x‖ := by
  have he : ‖doubleL2Map μ x‖^2 = ‖x‖^2 := by
    rw [l2_norm_sq_integral]
    have hfun : (fun s => ‖doubleL2Map μ x s‖^2) =ᵐ[doubleMeasure μ]
        (fun s => ‖doubleFunction μ x s‖^2) :=
      (doubleL2Map_coeFn μ x).mono fun s hs => by
        change ‖doubleL2Map μ x s‖^2 = ‖doubleFunction μ x s‖^2
        rw [hs]
    rw [integral_congr_ae hfun]
    have hi := (memLp_two_iff_integrable_sq_norm (doubleFunction_memLp μ x).aestronglyMeasurable).mp
      (doubleFunction_memLp μ x)
    rw [doubleMeasure, integral_add_measure hi.left_of_add_measure hi.right_of_add_measure,
      inl_measurableEmbedding.integral_map, inr_measurableEmbedding.integral_map,
      WithLp.prod_norm_sq_eq_of_L2, l2_norm_sq_integral, l2_norm_sq_integral]
    rfl
  nlinarith [norm_nonneg (doubleL2Map μ x), norm_nonneg x]

theorem doubleL2Map_surjective : Function.Surjective (doubleL2Map μ) := by
  intro v
  have hl : MemLp (fun x => v (Sum.inl x)) 2 μ :=
    inl_measurableEmbedding.memLp_map_measure_iff.mp (Lp.memLp v).left_of_add_measure
  have hr : MemLp (fun x => v (Sum.inr x)) 2 μ :=
    inr_measurableEmbedding.memLp_map_measure_iff.mp (Lp.memLp v).right_of_add_measure
  let x := pairL2 (hl.toLp _) (hr.toLp _)
  refine ⟨x, ?_⟩
  apply Lp.ext
  apply (doubleL2Map_coeFn μ x).trans
  exact (double_ae_iff μ).mpr ⟨hl.coeFn_toLp,hr.coeFn_toLp⟩

def doubleL2Equiv : SumL2 (L2 μ) ≃ₗᵢ[ℂ] L2 (doubleMeasure μ) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := doubleL2Map μ, norm_map' := doubleL2Map_norm μ }
    (doubleL2Map_surjective μ)

theorem doubleL2Equiv_modEq (x y : SumL2 (L2 μ)) :
    ModEq (doubleL2Equiv μ x) (doubleL2Equiv μ y) ↔ PairModEq x y := by
  change (∀ᵐ s ∂doubleMeasure μ, ‖doubleL2Map μ x s‖ = ‖doubleL2Map μ y s‖) ↔ _
  have he : (∀ᵐ s ∂doubleMeasure μ, ‖doubleL2Map μ x s‖ = ‖doubleL2Map μ y s‖) ↔
      (∀ᵐ s ∂doubleMeasure μ, ‖doubleFunction μ x s‖ = ‖doubleFunction μ y s‖) := by
    apply Filter.eventually_congr
    filter_upwards [doubleL2Map_coeFn μ x,doubleL2Map_coeFn μ y] with s hx hy
    rw [hx,hy]
  rw [he,double_ae_iff]
  rfl

theorem doubleMeasure_finite [IsFiniteMeasure μ] : IsFiniteMeasure (doubleMeasure μ) := by
  unfold doubleMeasure
  infer_instance

theorem doubleMeasure_ne_zero [NeZero μ] : doubleMeasure μ ≠ 0 := by
  intro h
  have he : doubleMeasure μ (range (@Sum.inl X X)) = μ univ := by
    simp [doubleMeasure, Measure.add_apply, inl_measurableEmbedding.map_apply,
      inr_measurableEmbedding.map_apply]
  rw [h] at he
  simp only [Measure.coe_zero, Pi.zero_apply] at he
  exact (NeZero.ne μ) (Measure.measure_univ_eq_zero.mp he.symm)

theorem doubleMeasure_noAtoms [NullSingletonClass μ] : NullSingletonClass (doubleMeasure μ) := by
  constructor
  intro x
  cases x <;> simp [doubleMeasure, Measure.add_apply, inl_measurableEmbedding.map_apply,
    inr_measurableEmbedding.map_apply, Set.preimage]

end OperatorPhaseRetrieval

end
