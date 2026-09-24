import OperatorPhaseRetrieval.L2

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

/-! Change of measure by multiplication with the square root of the density. -/
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorPhaseRetrieval
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem l2_norm_sq_integral (u : L2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq u, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => real_inner_self_eq_norm_sq (u x)

def densityRoot (f : X → ℝ≥0) (x : X) : ℂ := (Real.sqrt (f x) : ℝ)

omit [MeasurableSpace X] in
theorem densityRoot_sq (f : X → ℝ≥0) (x : X) (z : ℂ) :
    ‖densityRoot f x * z‖^2 = (f x : ℝ) * ‖z‖^2 := by
  simp only [densityRoot, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (NNReal.coe_nonneg _)]

theorem densityRoot_measurable {f : X → ℝ≥0} (hf : Measurable f) : Measurable (densityRoot f) :=
  Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hf.coe_nnreal_real)

theorem density_ac {f : X → ℝ≥0} (hf : Measurable f) (hpos : ∀ᵐ x ∂μ, f x ≠ 0) :
    μ ≪ μ.withDensity (fun x => (f x : ℝ≥0∞)) :=
  withDensity_absolutelyContinuous' hf.coe_nnreal_ennreal.aemeasurable
    (hpos.mono fun x hx => by exact_mod_cast hx)

theorem memLp_densityRoot {f : X → ℝ≥0} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂μ, f x ≠ 0) (u : L2 (μ.withDensity (fun x => (f x : ℝ≥0∞)))) :
    MemLp (fun x => densityRoot f x * u x) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    ((densityRoot_measurable hf).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable u).mono_ac (density_ac hf hpos)))).mpr
  have hi := (integrable_withDensity_iff_integrable_smul hf).mp
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u))
  change Integrable (fun x => ‖densityRoot f x * u x‖^2) μ
  simpa only [densityRoot_sq, NNReal.smul_def, smul_eq_mul] using hi

def densityL2Map {f : X → ℝ≥0} (hf : Measurable f) (hpos : ∀ᵐ x ∂μ, f x ≠ 0) :
    L2 (μ.withDensity (fun x => (f x : ℝ≥0∞))) →ₗ[ℂ] L2 μ where
  toFun u := (memLp_densityRoot hf hpos u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(memLp_densityRoot hf hpos (u+v)).coeFn_toLp,
      (memLp_densityRoot hf hpos u).coeFn_toLp, (memLp_densityRoot hf hpos v).coeFn_toLp,
      Lp.coeFn_add ((memLp_densityRoot hf hpos u).toLp _) ((memLp_densityRoot hf hpos v).toLp _),
      (density_ac hf hpos).ae_le (Lp.coeFn_add u v)] with x huv hu hv hadd huadd
    simp only [Pi.add_apply] at hadd huadd
    rw [huv,hadd,hu,hv,huadd]
    exact mul_add _ _ _
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(memLp_densityRoot hf hpos (c • u)).coeFn_toLp,
      (memLp_densityRoot hf hpos u).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_densityRoot hf hpos u).toLp _),
      (density_ac hf hpos).ae_le (Lp.coeFn_smul c u)] with x hcu hu hsmul hcu'
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hsmul hcu'
    rw [hcu,hsmul,hu,hcu']
    change densityRoot f x * (c * u x) = c * (densityRoot f x * u x)
    ring

theorem densityL2Map_coeFn {f : X → ℝ≥0} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂μ, f x ≠ 0) (u : L2 (μ.withDensity (fun x => (f x : ℝ≥0∞)))) :
    (densityL2Map hf hpos u : X → ℂ) =ᵐ[μ] fun x => densityRoot f x * u x :=
  (memLp_densityRoot hf hpos u).coeFn_toLp

theorem densityL2Map_norm {f : X → ℝ≥0} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂μ, f x ≠ 0) (u : L2 (μ.withDensity (fun x => (f x : ℝ≥0∞)))) :
    ‖densityL2Map hf hpos u‖ = ‖u‖ := by
  have he : ‖densityL2Map hf hpos u‖^2 = ‖u‖^2 := by
    rw [l2_norm_sq_integral, l2_norm_sq_integral,
      integral_withDensity_eq_integral_smul hf]
    apply integral_congr_ae
    filter_upwards [densityL2Map_coeFn hf hpos u] with x hx
    rw [hx,densityRoot_sq]
    rfl
  nlinarith [norm_nonneg (densityL2Map hf hpos u), norm_nonneg u]

omit [MeasurableSpace X] in
theorem densityRoot_ne_zero {f : X → ℝ≥0} {x : X} (hx : f x ≠ 0) : densityRoot f x ≠ 0 := by
  simp only [densityRoot, Complex.ofReal_ne_zero]
  exact (Real.sqrt_pos.mpr (by exact_mod_cast pos_iff_ne_zero.mpr hx)).ne'

omit [MeasurableSpace X] in
theorem densityRoot_inv_sq {f : X → ℝ≥0} {x : X} (hx : f x ≠ 0) (z : ℂ) :
    (f x : ℝ) * ‖(densityRoot f x)⁻¹ * z‖^2 = ‖z‖^2 := by
  have he := densityRoot_sq f x ((densityRoot f x)⁻¹ * z)
  rw [← mul_assoc, mul_inv_cancel₀ (densityRoot_ne_zero hx), one_mul] at he
  exact he.symm

theorem densityL2Map_surjective {f : X → ℝ≥0} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂μ, f x ≠ 0) : Function.Surjective (densityL2Map hf hpos) := by
  intro v
  let g : X → ℂ := fun x => (densityRoot f x)⁻¹ * v x
  have hgm : AEStronglyMeasurable g (μ.withDensity (fun x => (f x : ℝ≥0∞))) :=
    (densityRoot_measurable hf).inv.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable v).mono_ac (withDensity_absolutelyContinuous _ _))
  have hglp : MemLp g 2 (μ.withDensity (fun x => (f x : ℝ≥0∞))) := by
    apply (memLp_two_iff_integrable_sq_norm hgm).mpr
    apply (integrable_withDensity_iff_integrable_smul hf).mpr
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
    apply hi.congr
    filter_upwards [hpos] with x hx
    exact (densityRoot_inv_sq hx (v x)).symm
  refine ⟨hglp.toLp g, ?_⟩
  apply Lp.ext
  filter_upwards [densityL2Map_coeFn hf hpos (hglp.toLp g),
    (density_ac hf hpos).ae_le hglp.coeFn_toLp, hpos] with x hx hg hp
  rw [hx,hg]
  change densityRoot f x * ((densityRoot f x)⁻¹ * v x) = v x
  rw [← mul_assoc, mul_inv_cancel₀ (densityRoot_ne_zero hp), one_mul]

def densityL2Equiv {f : X → ℝ≥0} (hf : Measurable f) (hpos : ∀ᵐ x ∂μ, f x ≠ 0) :
    L2 (μ.withDensity (fun x => (f x : ℝ≥0∞))) ≃ₗᵢ[ℂ] L2 μ :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := densityL2Map hf hpos, norm_map' := densityL2Map_norm hf hpos }
    (densityL2Map_surjective hf hpos)

theorem densityL2Equiv_modEq {f : X → ℝ≥0} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂μ, f x ≠ 0)
    (u v : L2 (μ.withDensity (fun x => (f x : ℝ≥0∞)))) :
    ModEq (densityL2Equiv hf hpos u) (densityL2Equiv hf hpos v) ↔ ModEq u v := by
  change ModEq (densityL2Map hf hpos u) (densityL2Map hf hpos v) ↔ ModEq u v
  constructor
  · intro h
    apply (withDensity_absolutelyContinuous μ (fun x => (f x : ℝ≥0∞))).ae_le
    filter_upwards [h,densityL2Map_coeFn hf hpos u,densityL2Map_coeFn hf hpos v,hpos]
      with x hx hu hv hp
    rw [hu,hv,norm_mul,norm_mul] at hx
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr (densityRoot_ne_zero hp)) hx
  · intro h
    filter_upwards [(density_ac hf hpos).ae_le h,
      densityL2Map_coeFn hf hpos u,densityL2Map_coeFn hf hpos v] with x hx hu hv
    rw [hu,hv,norm_mul,norm_mul,hx]

/-- Equivalent sigma-finite measures have a modulus-preserving weighted L2 unitary. -/
theorem equivalent_measures_unitary (ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    ∃ W : L2 ν ≃ₗᵢ[ℂ] L2 μ, ∀ u v, ModEq (W u) (W v) ↔ ModEq u v := by
  let f : X → ℝ≥0 := fun x => (ν.rnDeriv μ x).toNNReal
  have hf : Measurable f := (Measure.measurable_rnDeriv ν μ).ennreal_toNNReal
  have hpos : ∀ᵐ x ∂μ, f x ≠ 0 := by
    filter_upwards [hμν.ae_le (Measure.rnDeriv_pos hνμ), Measure.rnDeriv_lt_top ν μ]
      with x hx hxt
    exact (ENNReal.toNNReal_pos hx.ne' hxt.ne).ne'
  have he : μ.withDensity (fun x => (f x : ℝ≥0∞)) = ν := by
    calc
      _ = μ.withDensity (ν.rnDeriv μ) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
        exact ENNReal.coe_toNNReal hx.ne
      _ = ν := Measure.withDensity_rnDeriv_eq ν μ hνμ
  rw [← he]
  exact ⟨densityL2Equiv hf hpos, densityL2Equiv_modEq hf hpos⟩

end OperatorPhaseRetrieval

end
