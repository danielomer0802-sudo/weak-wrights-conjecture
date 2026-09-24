import OperatorPhaseRetrieval.ThreePhase

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate

/-!
# Positive-area uniqueness

The measure-theoretic step is proved by slicing and the one-dimensional
isolated-zeros theorem. No real-analytic zero-set theorem is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace OperatorPhaseRetrieval

/-- The one-dimensional zero-set lemma on an arbitrary connected set. -/
theorem analytic_real_zero_null_on {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {U : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hc : IsPreconnected U)
    (hne : ∃ x ∈ U, f x ≠ 0) : volume (U ∩ {x | f x = 0}) = 0 := by
  have hh : {x | f x ≠ 0} ∈ codiscreteWithin U := by
    rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hc with h | h
    · obtain ⟨x,hx,hne⟩ := hne
      exact (hne (h hx)).elim
    · exact h
  have hd := isDiscrete_of_codiscreteWithin (s := {x | f x ≠ 0}ᶜ) (by simpa using hh)
  have he : {x | f x ≠ 0}ᶜ ∩ U = U ∩ {x | f x = 0} := by ext x; simp [and_comm]
  rw [he] at hd
  exact ((HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd).measure_zero volume

/-- A separately analytic nonzero function has a null zero set on a closed
rectangle. This local version does not require regularity outside the rectangle. -/
theorem analytic_rectangle_zero_null {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hc : ContinuousOn f (Icc a b ×ˢ Icc c d))
    (hx : ∀ y ∈ Icc c d, AnalyticOnNhd ℝ (fun x => f (x,y)) (Icc a b))
    (hy : ∀ x ∈ Icc a b, AnalyticOnNhd ℝ (fun y => f (x,y)) (Icc c d))
    (hne : ∃ p ∈ Icc a b ×ˢ Icc c d, f p ≠ 0) :
    (volume : Measure ℝ).prod volume ((Icc a b ×ˢ Icc c d) ∩ {p | f p = 0}) = 0 := by
  obtain ⟨⟨x₀,y₀⟩, hmem, hne⟩ := hne
  have hs : MeasurableSet ((Icc a b ×ˢ Icc c d) ∩ {p | f p = 0}) :=
    (hc.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_Icc)
      isClosed_singleton).measurableSet
  apply (Measure.measure_prod_null hs).2
  have hz := analytic_real_zero_null_on (hx y₀ hmem.2) (convex_Icc a b).isPreconnected
    ⟨x₀,hmem.1,hne⟩
  have ha : ∀ᵐ x ∂volume, x ∈ Icc a b → f (x,y₀) ≠ 0 := by
    apply ae_iff.mpr
    simpa only [Classical.not_imp, not_not, ofPred_and, ofPred_mem_eq] using hz
  filter_upwards [ha] with x h
  change volume (Prod.mk x ⁻¹' ((Icc a b ×ˢ Icc c d) ∩ {p | f p = 0})) = 0
  by_cases hxi : x ∈ Icc a b
  · have hz' := analytic_real_zero_null_on (hy x hxi) (convex_Icc c d).isPreconnected
      ⟨y₀,hmem.2,h hxi⟩
    have he : Prod.mk x ⁻¹' ((Icc a b ×ˢ Icc c d) ∩ {p | f p = 0}) =
        Icc c d ∩ {y | f (x,y) = 0} := by
      ext y
      simp only [mem_preimage, mem_inter_iff, mem_prod, mem_ofPred_eq, hxi, true_and]
    rw [he]
    exact hz'
  · have he : Prod.mk x ⁻¹' ((Icc a b ×ˢ Icc c d) ∩ {p | f p = 0}) = ∅ := by
      ext y
      simp only [mem_preimage, mem_inter_iff, mem_prod, mem_ofPred_eq, hxi,
        false_and, mem_empty_iff_false]
    rw [he, measure_empty]

/-- Local-to-global nullity of the zeros of a real-analytic function on an
open connected planar domain. -/
theorem analytic_plane_zero_null_on {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hf : AnalyticOnNhd ℝ f U) (ho : IsOpen U) (hc : IsPreconnected U)
    (hne : ∃ p ∈ U, f p ≠ 0) :
    (volume : Measure ℝ).prod volume (U ∩ {p | f p = 0}) = 0 := by
  apply measure_null_of_locally_null
  intro z hz
  obtain ⟨r,hr,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds hz.1)
  have hbr : Metric.closedBall z r ∈ 𝓝 z := Metric.closedBall_mem_nhds z hr
  have hneR : ∃ p ∈ Metric.closedBall z r, f p ≠ 0 := by
    by_contra! hn
    have he : f =ᶠ[𝓝 z] 0 := by
      filter_upwards [hbr] with p hp
      exact hn p hp
    have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hz.1 he
    obtain ⟨p,hp,hpn⟩ := hne
    exact hpn (hall hp)
  have hball : Metric.closedBall z r =
      Icc (z.1-r) (z.1+r) ×ˢ Icc (z.2-r) (z.2+r) := by
    rw [← closedBall_prod_same z.1 z.2 r, Real.closedBall_eq_Icc,
      Real.closedBall_eq_Icc]
  have hzR : (volume : Measure ℝ).prod volume
      (Metric.closedBall z r ∩ {p | f p = 0}) = 0 := by
    rw [hball] at hsub hneR ⊢
    apply analytic_rectangle_zero_null (hf.continuousOn.mono hsub)
    · intro y hy x hx
      exact (hf (x,y) (hsub ⟨hx,hy⟩)).comp (f := fun t : ℝ => (t,y))
        (analyticAt_id.prod analyticAt_const)
    · intro x hx y hy
      exact (hf (x,y) (hsub ⟨hx,hy⟩)).comp (analyticAt_const.prod analyticAt_id)
    · exact hneR
  refine ⟨Metric.closedBall z r ∩ (U ∩ {p | f p = 0}), ?_, ?_⟩
  · exact inter_mem (mem_nhdsWithin_of_mem_nhds hbr) self_mem_nhdsWithin
  · apply measure_mono_null _ hzR
    intro p hp
    exact ⟨hp.1,hp.2.2⟩

/-- A nonzero real-analytic function on the real line has a null zero set. -/
theorem analytic_real_ae_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : AnalyticOnNhd ℝ f univ)
    (hne : ∃ x, f x ≠ 0) : ∀ᵐ x ∂volume, f x ≠ 0 := by
  have hc : {x | f x ≠ 0} ∈ codiscrete ℝ := by
    rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
    · obtain ⟨x, hx⟩ := hne
      exact (hx (h (mem_univ x))).elim
    · exact h
  have hd := (mem_codiscrete'.mp hc).2
  have he : {x | f x ≠ 0}ᶜ = {x | f x = 0} := by ext x; simp
  rw [he] at hd
  have hcount : {x | f x = 0}.Countable := by
    exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd
  exact ae_iff.mpr (by simpa using hcount.measure_zero (volume : Measure ℝ))

/-- Separate real analyticity suffices for the planar zero-set argument. -/
theorem separately_analytic_ae_ne_zero {f : ℝ × ℝ → ℝ}
    (hc : Continuous f)
    (hx : ∀ y, AnalyticOnNhd ℝ (fun x => f (x,y)) univ)
    (hy : ∀ x, AnalyticOnNhd ℝ (fun y => f (x,y)) univ)
    (hne : ∃ p, f p ≠ 0) : ∀ᵐ p ∂(volume : Measure ℝ).prod volume, f p ≠ 0 := by
  obtain ⟨⟨x₀,y₀⟩, h₀⟩ := hne
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_eq hc continuous_const).measurableSet.compl).2
  filter_upwards [analytic_real_ae_ne_zero (hx y₀) ⟨x₀,h₀⟩] with x h
  exact analytic_real_ae_ne_zero (hy x) ⟨y₀,h⟩

/-- A globally real-analytic nonzero function on the plane is nonzero a.e. -/
theorem analytic_plane_ae_ne_zero {f : ℝ × ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f univ) (hne : ∃ p, f p ≠ 0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod volume, f p ≠ 0 := by
  apply separately_analytic_ae_ne_zero (continuous_iff_continuousAt.mpr
    (fun p => (hf p (mem_univ p)).continuousAt))
  · intro y x _
    exact (hf (x,y) (mem_univ _)).comp (f := fun t : ℝ => (t,y))
      (analyticAt_id.prod analyticAt_const)
  · intro x y _
    exact (hf (x,y) (mem_univ _)).comp (analyticAt_const.prod analyticAt_id)
  · exact hne

/-- The same null-set result in complex coordinates, for real analyticity. -/
theorem analytic_complex_ae_ne_zero {f : ℂ → ℝ}
    (hf : AnalyticOnNhd ℝ f univ) (hne : ∃ z, f z ≠ 0) :
    ∀ᵐ z ∂volume, f z ≠ 0 := by
  have hp : AnalyticOnNhd ℝ (fun p => f (Complex.equivRealProdCLM.symm p)) univ := by
    intro p _
    exact (hf _ (mem_univ _)).comp (Complex.equivRealProdCLM.symm.analyticAt p)
  have hn : ∃ p, f (Complex.equivRealProdCLM.symm p) ≠ 0 := by
    obtain ⟨z,hz⟩ := hne
    exact ⟨Complex.equivRealProdCLM z, by
      rwa [ContinuousLinearEquiv.symm_apply_apply]⟩
  have hh := analytic_plane_ae_ne_zero hp hn
  have hm := Complex.volume_preserving_equiv_real_prod
  have ht := hm.quasiMeasurePreserving.ae hh
  change ∀ᵐ z ∂volume, f (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z)) ≠ 0 at ht
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using ht

/-- Real-analytic zero-set nullity on an open connected complex domain. -/
theorem analytic_complex_zero_null_on {f : ℂ → ℝ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℝ f U) (ho : IsOpen U) (hc : IsPreconnected U)
    (hne : ∃ z ∈ U, f z ≠ 0) : volume (U ∩ {z | f z = 0}) = 0 := by
  let e := Complex.equivRealProdCLM
  let V := e.symm ⁻¹' U
  have hp : AnalyticOnNhd ℝ (fun p => f (e.symm p)) V := by
    intro p hp
    exact (hf _ hp).comp (e.symm.analyticAt p)
  have hVo : IsOpen V := ho.preimage e.symm.continuous
  have hVc : IsPreconnected V := e.symm.toHomeomorph.isPreconnected_preimage.mpr hc
  have hn : ∃ p ∈ V, f (e.symm p) ≠ 0 := by
    obtain ⟨z,hz,hzn⟩ := hne
    exact ⟨e z, by simpa [V] using hz, by simpa using hzn⟩
  have hnul := analytic_plane_zero_null_on hp hVo hVc hn
  have hae : ∀ᵐ p ∂(volume : Measure ℝ).prod volume, ¬(p ∈ V ∧ f (e.symm p) = 0) := by
    exact ae_iff.mpr (by simpa only [not_not, ofPred_and, ofPred_mem_eq] using hnul)
  have ha := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hae
  have ha' : ∀ᵐ z ∂volume, ¬(z ∈ U ∧ f z = 0) := by
    change ∀ᵐ z ∂volume, ¬(e.symm (e z) ∈ U ∧ f (e.symm (e z)) = 0) at ha
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using ha
  simpa only [not_not, ofPred_and, ofPred_mem_eq] using ae_iff.mp ha'

theorem analytic_normSq_on {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℝ (fun z => Complex.normSq (F z)) U := by
  intro z hz
  have h : AnalyticAt ℝ F z := (hF z hz).restrictScalars
  have hr := (Complex.reCLM.analyticAt (F z)).comp h
  have hi := (Complex.imCLM.analyticAt (F z)).comp h
  convert (hr.mul hr).add (hi.mul hi) using 1 <;> rfl

theorem analytic_normSq {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ) :
    AnalyticOnNhd ℝ (fun z => Complex.normSq (F z)) univ := by
  intro z _
  have h : AnalyticAt ℝ F z := (hF z (mem_univ z)).restrictScalars
  have hr := (Complex.reCLM.analyticAt (F z)).comp h
  have hi := (Complex.imCLM.analyticAt (F z)).comp h
  convert (hr.mul hr).add (hi.mul hi) using 1 <;> rfl

/-- Positive area equality of entire-function moduli propagates everywhere. -/
theorem entire_norm_eq_of_positive_measure {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (hpos : 0 < volume {z | ‖F z‖ = ‖G z‖}) : ∀ z, ‖F z‖ = ‖G z‖ := by
  by_contra hn
  push Not at hn
  have hneq : ∃ z, Complex.normSq (F z) - Complex.normSq (G z) ≠ 0 := by
    obtain ⟨z,hz⟩ := hn
    refine ⟨z, ?_⟩
    intro h
    apply hz
    have hsq : ‖F z‖ ^ 2 = ‖G z‖ ^ 2 := by
      simpa only [Complex.normSq_eq_norm_sq, sub_eq_zero] using h
    nlinarith [norm_nonneg (F z), norm_nonneg (G z)]
  have hae := analytic_complex_ae_ne_zero ((analytic_normSq hF).sub (analytic_normSq hG)) hneq
  have hzero : volume {z | ‖F z‖ = ‖G z‖} = 0 := by
    apply measure_mono_null (t := {z | Complex.normSq (F z) - Complex.normSq (G z) = 0})
    · intro z hz
      change ‖F z‖ = ‖G z‖ at hz
      simp only [mem_ofPred_eq, Complex.normSq_eq_norm_sq, hz, sub_self]
    · simpa only [not_not, Pi.sub_apply] using ae_iff.mp hae
  exact (ne_of_gt hpos) hzero

/-- On a connected open domain, holomorphic functions with equal moduli
differ by one constant scalar of norm one. -/
theorem holomorphic_phase_of_norm_eq {F G : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (ho : IsOpen U) (hc : IsPreconnected U)
    (hn : ∀ z ∈ U, ‖F z‖ = ‖G z‖) :
    ∃ ω : ℂ, IsPhase ω ∧ EqOn G (fun z => ω * F z) U := by
  by_cases hz : ∀ z ∈ U, F z = 0
  · refine ⟨1, by simp [IsPhase], ?_⟩
    intro z hzu
    have : G z = 0 := norm_eq_zero.mp (by simpa [hz z hzu] using (hn z hzu).symm)
    simp [this, hz z hzu]
  push Not at hz
  obtain ⟨z₀,hz₀,hF₀⟩ := hz
  let ω := G z₀ / F z₀
  have hω : IsPhase ω := by
    change ‖G z₀ / F z₀‖ = 1
    rw [norm_div, ← hn z₀ hz₀, div_self (norm_ne_zero_iff.mpr hF₀)]
  have hlocal : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ F z ≠ 0 :=
    Filter.Eventually.and (ho.mem_nhds hz₀) ((hF z₀ hz₀).continuousAt.eventually_ne hF₀)
  have hd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (fun z => G z / F z) z := by
    filter_upwards [hlocal] with z hz
    exact (hG z hz.1).differentiableAt.div (hF z hz.1).differentiableAt hz.2
  have hm : IsLocalMax (norm ∘ (fun z => G z / F z)) z₀ := by
    filter_upwards [hlocal] with z hz
    change ‖G z / F z‖ ≤ ‖ω‖
    rw [show ‖ω‖ = 1 from hω, norm_div, ← hn z hz.1,
      div_self (norm_ne_zero_iff.mpr hz.2)]
  have he := Complex.eventually_eq_of_isLocalMax_norm hd hm
  refine ⟨ω, hω, hG.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const.mul hF) hc hz₀ ?_⟩
  filter_upwards [he, hlocal] with z hz hzu
  exact (div_eq_iff hzu.2).mp hz

/-- Lemma 3.1 for entire functions: positive-area modulus agreement fixes
one global phase. This is the form needed for the smoothing construction. -/
theorem entire_phase_of_positive_measure {F G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (hpos : 0 < volume {z | ‖F z‖ = ‖G z‖}) :
    ∃ ω : ℂ, IsPhase ω ∧ ∀ z, G z = ω * F z := by
  obtain ⟨ω,hω,h⟩ := holomorphic_phase_of_norm_eq hF hG isOpen_univ
    isPreconnected_univ (fun z _ => entire_norm_eq_of_positive_measure hF hG hpos z)
  exact ⟨ω,hω,fun z => h (mem_univ z)⟩

/-- Lemma 3.1 on an arbitrary connected open domain, with the agreement
set measured in planar Lebesgue measure. -/
theorem holomorphic_phase_of_positive_measure {F G : ℂ → ℂ} {U : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (ho : IsOpen U) (hc : IsPreconnected U)
    (hpos : 0 < volume (U ∩ {z | ‖F z‖ = ‖G z‖})) :
    ∃ ω : ℂ, IsPhase ω ∧ EqOn G (fun z => ω * F z) U := by
  apply holomorphic_phase_of_norm_eq hF hG ho hc
  by_contra! hn
  obtain ⟨z,hzu,hz⟩ := hn
  have hneq : Complex.normSq (F z) - Complex.normSq (G z) ≠ 0 := by
    intro h
    apply hz
    have hsq : ‖F z‖ ^ 2 = ‖G z‖ ^ 2 := by
      simpa only [Complex.normSq_eq_norm_sq, sub_eq_zero] using h
    nlinarith [norm_nonneg (F z), norm_nonneg (G z)]
  have hnull := analytic_complex_zero_null_on
    ((analytic_normSq_on hF).sub (analytic_normSq_on hG)) ho hc ⟨z,hzu,hneq⟩
  have hzero : volume (U ∩ {z | ‖F z‖ = ‖G z‖}) = 0 := by
    apply measure_mono_null _ hnull
    intro w hw
    have hnw : ‖F w‖ = ‖G w‖ := hw.2
    refine ⟨hw.1, ?_⟩
    change Complex.normSq (F w) - Complex.normSq (G w) = 0
    simp only [Complex.normSq_eq_norm_sq, hnw, sub_self]
  exact (ne_of_gt hpos) hzero

/-- The a.e.-agreement formulation of Lemma 3.1, including arbitrary
measurable positive-area subsets of the connected open domain. -/
theorem holomorphic_phase_of_ae_norm_eq {F G : ℂ → ℂ} {U S : Set ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (ho : IsOpen U) (hc : IsPreconnected U) (hS : MeasurableSet S)
    (hSU : S ⊆ U) (hpos : 0 < volume S)
    (he : ∀ᵐ z ∂volume.restrict S, ‖F z‖ = ‖G z‖) :
    ∃ ω : ℂ, IsPhase ω ∧ EqOn G (fun z => ω * F z) U := by
  apply holomorphic_phase_of_positive_measure hF hG ho hc
  apply hpos.trans_le
  apply measure_mono_ae
  filter_upwards [(ae_restrict_iff' hS).mp he] with z hz
  exact fun hzs => ⟨hSU hzs, hz hzs⟩

end OperatorPhaseRetrieval

end
