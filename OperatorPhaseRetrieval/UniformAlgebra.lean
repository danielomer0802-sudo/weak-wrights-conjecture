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

/-! Polynomial approximation on a compact planar set. -/
open Set Filter
open scoped Topology
namespace OperatorPhaseRetrieval
variable (K : Set ℂ) [CompactSpace K]

def coordinateMap : C(K, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

def uniformPolynomial : Polynomial ℂ →ₐ[ℂ] C(K, ℂ) :=
  Polynomial.aeval (coordinateMap K)

omit [CompactSpace ↑K] in
theorem uniformPolynomial_apply (p : Polynomial ℂ) (z : K) :
    uniformPolynomial K p z = p.eval (z : ℂ) := by
  change (ContinuousMap.evalAlgHom ℂ ℂ z) (Polynomial.aeval (coordinateMap K) p) = _
  rw [← Polynomial.aeval_algHom_apply]
  rfl

def uniformPolynomialClosure : Subalgebra ℂ C(K, ℂ) :=
  (uniformPolynomial K).range.topologicalClosure

theorem uniformPolynomial_mem (p : Polynomial ℂ) :
    uniformPolynomial K p ∈ uniformPolynomialClosure K :=
  Subalgebra.le_topologicalClosure _ ⟨p, rfl⟩

theorem coordinateMap_mem : coordinateMap K ∈ uniformPolynomialClosure K := by
  simpa [uniformPolynomial] using uniformPolynomial_mem K Polynomial.X

theorem uniformPolynomialClosure_closed :
    IsClosed (uniformPolynomialClosure K : Set C(K, ℂ)) :=
  Subalgebra.isClosed_topologicalClosure _

theorem coordinate_spectrum (hK : IsPreconnected Kᶜ) :
    spectrum ℂ (⟨coordinateMap K, coordinateMap_mem K⟩ : uniformPolynomialClosure K) = K := by
  let : IsClosed (uniformPolynomialClosure K : Set C(K, ℂ)) :=
    uniformPolynomialClosure_closed K
  have hr : range (coordinateMap K) = K := by
    exact Subtype.range_coe
  have hs : spectrum ℂ (coordinateMap K) = K :=
    (ContinuousMap.spectrum_eq_range _).trans hr
  rw [Subalgebra.spectrum_eq_of_isPreconnected_compl (uniformPolynomialClosure K) _
    (by simpa only [hs] using hK), hs]

theorem polynomial_isUnit_in_closure [Nonempty K] (hK : IsPreconnected Kᶜ)
    (p : Polynomial ℂ) (hp : ∀ z : K, p.eval (z : ℂ) ≠ 0) :
    IsUnit (⟨uniformPolynomial K p, uniformPolynomial_mem K p⟩ : uniformPolynomialClosure K) := by
  let : IsClosed (uniformPolynomialClosure K : Set C(K, ℂ)) :=
    uniformPolynomialClosure_closed K
  let : CompleteSpace (uniformPolynomialClosure K) :=
    (uniformPolynomialClosure_closed K).completeSpace_coe
  let Z : uniformPolynomialClosure K := ⟨coordinateMap K, coordinateMap_mem K⟩
  have hv : (Polynomial.aeval Z p : uniformPolynomialClosure K) =
      ⟨uniformPolynomial K p, uniformPolynomial_mem K p⟩ := by
    apply Subtype.ext
    change (uniformPolynomialClosure K).val (Polynomial.aeval Z p) = _
    rw [← Polynomial.aeval_algHom_apply]
    rfl
  rw [← hv, ← spectrum.zero_notMem_iff (R := ℂ), spectrum.map_polynomial_aeval, coordinate_spectrum K hK]
  rintro ⟨z, hz, he⟩
  exact hp ⟨z,hz⟩ he

/-- The polynomial closure is inverse closed when the complement is connected. -/
theorem uniformClosure_isUnit [Nonempty K] (hK : IsPreconnected Kᶜ)
    (g : uniformPolynomialClosure K) (hg : ∀ z : K, (g : C(K,ℂ)) z ≠ 0) :
    IsUnit g := by
  let : IsClosed (uniformPolynomialClosure K : Set C(K,ℂ)) :=
    uniformPolynomialClosure_closed K
  have hc : (g : C(K,ℂ)) ∈ closure ((uniformPolynomial K).range : Set C(K,ℂ)) := g.property
  obtain ⟨f, hf, ht⟩ := mem_closure_iff_seq_limit.mp hc
  let fs : ℕ → uniformPolynomialClosure K := fun n =>
    ⟨f n, Subalgebra.le_topologicalClosure _ (hf n)⟩
  have hts : Tendsto fs atTop (𝓝 g) := tendsto_subtype_rng.mpr ht
  have hgu : IsUnit (g : C(K,ℂ)) := (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr hg
  have heu : ∀ᶠ n in atTop, IsUnit (fs n) := by
    filter_upwards [ht.eventually (Units.isOpen.mem_nhds hgu)] with n hn
    obtain ⟨p,hp⟩ := hf n
    change uniformPolynomial K p = f n at hp
    have hpu : ∀ z : K, p.eval (z : ℂ) ≠ 0 := by
      intro z
      rw [← uniformPolynomial_apply K p z, hp]
      exact (ContinuousMap.isUnit_iff_forall_ne_zero _).mp hn z
    have hu := polynomial_isUnit_in_closure K hK p hpu
    convert hu using 1
    apply Subtype.ext
    exact hp.symm
  exact Subalgebra.isUnit_of_isUnit_val_of_eventually (uniformPolynomialClosure K)
    hgu hts heu inferInstance

/-- The pointwise reciprocal belongs to the same closed polynomial algebra. -/
theorem uniformClosure_inverse [Nonempty K] (hK : IsPreconnected Kᶜ)
    (g : C(K,ℂ)) (hgm : g ∈ uniformPolynomialClosure K) (hg : ∀ z, g z ≠ 0) :
    ∃ r : C(K,ℂ), r ∈ uniformPolynomialClosure K ∧ ∀ z, r z = (g z)⁻¹ := by
  let u := (uniformClosure_isUnit K hK ⟨g,hgm⟩ hg).unit
  refine ⟨((↑u⁻¹ : uniformPolynomialClosure K) : C(K,ℂ)), (↑u⁻¹ : uniformPolynomialClosure K).property, ?_⟩
  intro z
  have he := congrArg (fun f : uniformPolynomialClosure K => (f : C(K,ℂ)) z) u.mul_inv
  change g z * (((↑u⁻¹ : uniformPolynomialClosure K) : C(K,ℂ)) z) = 1 at he
  exact inv_eq_of_mul_eq_one_right he |>.symm

/-- Exponentiation stays in a closed polynomial algebra. -/
theorem uniformClosure_exp (g : C(K,ℂ)) (hg : g ∈ uniformPolynomialClosure K) :
    ∃ e : C(K,ℂ), e ∈ uniformPolynomialClosure K ∧ ∀ z, e z = Complex.exp (g z) := by
  refine ⟨NormedSpace.exp g,
    NormedSpace.exp_mem (R := ℂ) (uniformPolynomialClosure_closed K) hg, ?_⟩
  intro z
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ z)
    (continuous_eval_const z) g
  simpa only [ContinuousMap.evalAlgHom_apply, ← Complex.exp_eq_exp_ℂ] using he

end OperatorPhaseRetrieval

end
