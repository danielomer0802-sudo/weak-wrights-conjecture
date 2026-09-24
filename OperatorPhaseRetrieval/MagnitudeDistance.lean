import OperatorPhaseRetrieval.AmplificationTheorem
import OperatorPhaseRetrieval.Instability

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

/-! Spatial unitaries preserve L2 distances between modulus functions. -/
open MeasureTheory
namespace OperatorPhaseRetrieval

def alignScalar (a b : ℂ) : ℂ := if a = 0 then b else (‖b‖/‖a‖ : ℝ) • a

theorem alignScalar_norm (a b : ℂ) : ‖alignScalar a b‖ = ‖b‖ := by
  by_cases ha : a = 0
  · simp [alignScalar, ha]
  · rw [alignScalar, if_neg ha, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg b) (norm_nonneg a)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr ha)]

theorem alignScalar_distance (a b : ℂ) : ‖a - alignScalar a b‖ = |‖a‖ - ‖b‖| := by
  by_cases ha : a = 0
  · simp [alignScalar,ha]
  · rw [alignScalar, if_neg ha]
    have he : a - (‖b‖/‖a‖ : ℝ) • a = (1-‖b‖/‖a‖ : ℝ) • a := by module
    rw [he,norm_smul,Real.norm_eq_abs]
    calc
      _ = |(1-‖b‖/‖a‖)*‖a‖| := by rw [abs_mul,abs_of_nonneg (norm_nonneg a)]
      _ = _ := by congr 1; field_simp [norm_ne_zero_iff.mpr ha]

theorem magnitude_eq_of_modEq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : L2 μ} (h : ModEq f g) : magnitude f = magnitude g := by
  apply Lp.ext
  filter_upwards [h,magnitude_coeFn f,magnitude_coeFn g] with x hx hf hg
  rw [hf,hg,hx]

theorem exists_magnitude_aligned {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g : L2 μ) :
    ∃ h : L2 μ, ModEq h g ∧ ‖f-h‖ = ‖magnitude f - magnitude g‖ := by
  have hm : Measurable (fun x => alignScalar (f x) (g x)) := by
    apply Measurable.ite ((Lp.stronglyMeasurable f).measurable (measurableSet_singleton 0))
      (Lp.stronglyMeasurable g).measurable
    exact ((Lp.stronglyMeasurable g).measurable.norm.div
      (Lp.stronglyMeasurable f).measurable.norm).smul (Lp.stronglyMeasurable f).measurable
  have hlp : MemLp (fun x => alignScalar (f x) (g x)) 2 μ :=
    (Lp.memLp g).of_le hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (alignScalar_norm (f x) (g x)).le)
  let h := hlp.toLp (fun x => alignScalar (f x) (g x))
  refine ⟨h, ?_, ?_⟩
  · filter_upwards [hlp.coeFn_toLp] with x hx
    change ‖h x‖ = ‖g x‖
    rw [hx,alignScalar_norm]
  · have he : ∀ᵐ x ∂μ, ‖(f-h) x‖ = ‖(magnitude f - magnitude g) x‖ := by
      filter_upwards [Lp.coeFn_sub f h,hlp.coeFn_toLp,
        Lp.coeFn_sub (magnitude f) (magnitude g),magnitude_coeFn f,magnitude_coeFn g]
        with x hx hh hmag hf hg
      simp only [Pi.sub_apply] at hx hmag
      rw [hx,hh,hmag,hf,hg,alignScalar_distance,Real.norm_eq_abs]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.le))
      (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.ge))

theorem spatial_magnitudeDistance_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (W : L2 μ ≃ₗᵢ[ℂ] L2 ν)
    (hW : ∀ f g, ModEq f g → ModEq (W f) (W g)) (f g : L2 μ) :
    ‖magnitude (W f) - magnitude (W g)‖ ≤ ‖magnitude f - magnitude g‖ := by
  obtain ⟨h,hh,hd⟩ := exists_magnitude_aligned f g
  rw [← magnitude_eq_of_modEq (hW h g hh)]
  calc
    _ ≤ ‖W f-W h‖ := magnitude_sub_le _ _
    _ = ‖f-h‖ := by rw [← W.map_sub,W.norm_map]
    _ = _ := hd

theorem spatial_magnitudeDistance {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (W : L2 μ ≃ₗᵢ[ℂ] L2 ν)
    (hW : ∀ f g, ModEq (W f) (W g) ↔ ModEq f g) (f g : L2 μ) :
    ‖magnitude (W f) - magnitude (W g)‖ = ‖magnitude f - magnitude g‖ := by
  apply le_antisymm (spatial_magnitudeDistance_le W (fun f g => (hW f g).mpr) f g)
  have hs : ∀ f g, ModEq f g → ModEq (W.symm f) (W.symm g) := by
    intro f g h
    exact (hW (W.symm f) (W.symm g)).mp (by simpa using h)
  simpa using spatial_magnitudeDistance_le W.symm hs (W f) (W g)


theorem pairMagnitude_eq_of_pairModEq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {x y : SumL2 (L2 μ)} (h : PairModEq x y) : pairMagnitude x = pairMagnitude y := by
  apply (WithLp.equiv 2 (Lp ℝ 2 μ × Lp ℝ 2 μ)).injective
  exact Prod.ext (magnitude_eq_of_modEq h.1) (magnitude_eq_of_modEq h.2)

theorem pairMagnitude_sub_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (x y : SumL2 (L2 μ)) : ‖pairMagnitude x - pairMagnitude y‖ ≤ ‖x-y‖ := by
  have h₁ := pow_le_pow_left₀ (norm_nonneg _) (magnitude_sub_le x.fst y.fst) 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg _) (magnitude_sub_le x.snd y.snd) 2
  have ha := WithLp.prod_norm_sq_eq_of_L2 (pairMagnitude x - pairMagnitude y)
  have hb := WithLp.prod_norm_sq_eq_of_L2 (x-y)
  simp only [WithLp.sub_fst,WithLp.sub_snd,pairMagnitude,pairL2_fst,pairL2_snd] at ha hb
  change ‖pairMagnitude x - pairMagnitude y‖^2 = _ at ha
  nlinarith [norm_nonneg (x-y),norm_nonneg (pairMagnitude x - pairMagnitude y)]

theorem exists_pair_magnitude_aligned {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (x y : SumL2 (L2 μ)) :
    ∃ z : SumL2 (L2 μ), PairModEq z y ∧ ‖x-z‖ = ‖pairMagnitude x-pairMagnitude y‖ := by
  obtain ⟨a,ha,hda⟩ := exists_magnitude_aligned x.fst y.fst
  obtain ⟨b,hb,hdb⟩ := exists_magnitude_aligned x.snd y.snd
  refine ⟨pairL2 a b,⟨ha,hb⟩,?_⟩
  have h₁ := WithLp.prod_norm_sq_eq_of_L2 (x-pairL2 a b)
  have h₂ := WithLp.prod_norm_sq_eq_of_L2 (pairMagnitude x-pairMagnitude y)
  simp only [WithLp.sub_fst,WithLp.sub_snd,pairMagnitude,pairL2_fst,pairL2_snd] at h₁ h₂
  change ‖pairMagnitude x - pairMagnitude y‖^2 = _ at h₂
  rw [hda,hdb] at h₁
  nlinarith [norm_nonneg (x-pairL2 a b),norm_nonneg (pairMagnitude x-pairMagnitude y)]

theorem pair_spatial_magnitudeDistance {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (W : L2 ν ≃ₗᵢ[ℂ] SumL2 (L2 μ))
    (hW : ∀ f g, PairModEq (W f) (W g) ↔ ModEq f g) (f g : L2 ν) :
    ‖pairMagnitude (W f)-pairMagnitude (W g)‖ = ‖magnitude f-magnitude g‖ := by
  apply le_antisymm
  · obtain ⟨h,hh,hd⟩ := exists_magnitude_aligned f g
    rw [← pairMagnitude_eq_of_pairModEq ((hW h g).mpr hh)]
    calc
      _ ≤ ‖W f-W h‖ := pairMagnitude_sub_le _ _
      _ = ‖f-h‖ := by rw [← W.map_sub,W.norm_map]
      _ = _ := hd
  · obtain ⟨x,hx,hd⟩ := exists_pair_magnitude_aligned (W f) (W g)
    have hm : ModEq (W.symm x) g := (hW _ _).mp (by simpa using hx)
    rw [← magnitude_eq_of_modEq hm]
    calc
      _ ≤ ‖f-W.symm x‖ := magnitude_sub_le _ _
      _ = ‖W f-x‖ := by rw [← W.norm_map (f-W.symm x),W.map_sub,W.apply_symm_apply]
      _ = _ := hd

end OperatorPhaseRetrieval

end
