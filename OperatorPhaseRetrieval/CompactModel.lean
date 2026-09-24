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

/-! A concrete positive-area compact product with irrational coordinates. -/
open MeasureTheory Set
namespace OperatorPhaseRetrieval

theorem exists_irrational_compact :
    ∃ F : Set ℝ, IsCompact F ∧ F ⊆ Ioo 0 1 ∧
      (∀ q : ℚ, (q : ℝ) ∉ F) ∧ 0 < volume F := by
  let Q : Set ℝ := range (fun q : ℚ => (q : ℝ))
  have hQ : Q.Countable := countable_range _
  have hV : volume (Ioo (0:ℝ) 1 \ Q) = 1 := by
    rw [measure_sdiff_null (hQ.measure_zero volume)]
    simp
  obtain ⟨F, hF, hc, hv⟩ := (measurableSet_Ioo.diff hQ.measurableSet).exists_lt_isCompact
    (μ := volume) (r := 0) (by rw [hV]; exact zero_lt_one)
  exact ⟨F, hc, fun x hx => (hF hx).1,
    fun q hq => (hF hq).2 ⟨q,rfl⟩, hv⟩

def planarProduct (F : Set ℝ) : Set ℂ := {z | z.re ∈ F ∧ z.im ∈ F}

theorem planarProduct_compact {F : Set ℝ} (hF : IsCompact F) :
    IsCompact (planarProduct F) := by
  have he : planarProduct F = Complex.equivRealProdCLM.symm '' (F ×ˢ F) := by
    ext z
    constructor
    · intro hz
      exact ⟨(z.re,z.im), hz, by simp [Complex.equivRealProdCLM_symm_apply]⟩
    · rintro ⟨⟨a,b⟩, hab, rfl⟩
      simpa [planarProduct, Complex.equivRealProdCLM_symm_apply] using hab
  rw [he]
  exact (hF.prod hF).image Complex.equivRealProdCLM.symm.continuous

theorem planarProduct_volume {F : Set ℝ} (hF : MeasurableSet F) :
    volume (planarProduct F) = volume F * volume F := by
  calc
    volume (planarProduct F) = volume (F ×ˢ F) :=
      Complex.volume_preserving_equiv_real_prod.measure_preimage (hF.prod hF).nullMeasurableSet
    _ = volume F * volume F := Measure.prod_prod F F

theorem joined_vertical_complement {F : Set ℝ} {x y : ℂ}
    (hx : x.re ∉ F) (he : x.re = y.re) :
    JoinedIn (planarProduct F)ᶜ x y := by
  apply JoinedIn.of_segment_subset
  rintro z ⟨a,b,ha,hb,hab,rfl⟩ hz
  apply hx
  have hr : (a • x + b • y).re = x.re := by
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, ← he]
    rw [← add_mul, hab, one_mul]
  rw [← hr]
  exact hz.1

theorem joined_horizontal_complement {F : Set ℝ} {x y : ℂ}
    (hx : x.im ∉ F) (he : x.im = y.im) :
    JoinedIn (planarProduct F)ᶜ x y := by
  apply JoinedIn.of_segment_subset
  rintro z ⟨a,b,ha,hb,hab,rfl⟩ hz
  apply hx
  have hi : (a • x + b • y).im = x.im := by
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, ← he]
    rw [← add_mul, hab, one_mul]
  rw [← hi]
  exact hz.2

theorem planarProduct_complement_pathConnected {F : Set ℝ} (h0 : (0:ℝ) ∉ F) :
    IsPathConnected (planarProduct F)ᶜ := by
  refine ⟨0, ?_, ?_⟩
  · exact fun h => h0 h.1
  · intro z hz
    by_cases hr : z.re ∈ F
    · have hi : z.im ∉ F := fun hi => hz ⟨hr,hi⟩
      have h₁ : JoinedIn (planarProduct F)ᶜ z (z.im * Complex.I) :=
        joined_horizontal_complement hi (by simp)
      have h₂ : JoinedIn (planarProduct F)ᶜ (z.im * Complex.I) 0 :=
        joined_vertical_complement (by simpa using h0) (by simp)
      exact (h₁.trans h₂).symm
    · have h₁ : JoinedIn (planarProduct F)ᶜ z (z.re : ℂ) :=
        joined_vertical_complement hr (by simp)
      have h₂ : JoinedIn (planarProduct F)ᶜ (z.re : ℂ) 0 :=
        joined_horizontal_complement (by simpa using h0) (by simp)
      exact (h₁.trans h₂).symm

theorem polynomials_memLp_compact {K : Set ℂ} (hK : IsCompact K) (p : Polynomial ℂ) :
    MemLp (fun z => p.eval z) 2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa using hK.measure_lt_top⟩
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn p.differentiable.continuous.continuousOn
  exact MemLp.of_bound p.differentiable.continuous.aestronglyMeasurable B
    (ae_restrict_mem hK.measurableSet |>.mono fun z hz => hB z hz)

end OperatorPhaseRetrieval

end
