import OperatorPhaseRetrieval.PolynomialSmoothing

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped Topology

/-! # From polynomial density to a polynomial Hilbert basis

The sole approximation input is density of the actual evaluation map into L2.
Gram--Schmidt, injectivity and all basis-to-smoothing steps are proved here.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorPhaseRetrieval
variable {μ : Measure ℂ}

def polynomialL2 (hm : ∀ p : Polynomial ℂ, MemLp (fun z => p.eval z) 2 μ) :
    Polynomial ℂ →ₗ[ℂ] L2 μ where
  toFun p := (hm p).toLp (fun z => p.eval z)
  map_add' p q := by
    apply Lp.ext
    filter_upwards [(hm (p+q)).coeFn_toLp, (hm p).coeFn_toLp, (hm q).coeFn_toLp,
      Lp.coeFn_add ((hm p).toLp _) ((hm q).toLp _)] with z hpq hp hq hadd
    rw [hpq, hadd]
    change (p+q).eval z = (hm p).toLp _ z + (hm q).toLp _ z
    rw [hp,hq,Polynomial.eval_add]
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [(hm (c • p)).coeFn_toLp, (hm p).coeFn_toLp,
      Lp.coeFn_smul c ((hm p).toLp _)] with z hcp hp hsmul
    change (hm (c • p)).toLp _ z = (c • (hm p).toLp _) z
    rw [hcp,hsmul]
    change (c • p).eval z = c * (hm p).toLp _ z
    rw [hp, Polynomial.smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]

theorem polynomialL2_coeFn (hm : ∀ p : Polynomial ℂ, MemLp (fun z => p.eval z) 2 μ)
    (p : Polynomial ℂ) : (polynomialL2 hm p : ℂ → ℂ) =ᵐ[μ] fun z => p.eval z :=
  (hm p).coeFn_toLp

theorem polynomialL2_injective [NeZero μ] (hμ : μ ≪ volume)
    (hm : ∀ p : Polynomial ℂ, MemLp (fun z => p.eval z) 2 μ) :
    Function.Injective (polynomialL2 hm) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  by_contra hpn
  have hn : μ {z | p.eval z = 0} = 0 :=
    hμ ((Polynomial.finite_setOfPred_isRoot hpn).measure_zero volume)
  have hne : ∀ᵐ z ∂μ, p.eval z ≠ 0 := ae_iff.mpr (by simpa using hn)
  have he := polynomialL2_coeFn hm p
  rw [hp] at he
  have hfalse : ∀ᵐ z ∂μ, False := by
    filter_upwards [he, hne, Lp.coeFn_zero ℂ 2 μ] with z hz hzn hz0
    exact hzn (hz.symm.trans hz0)
  exact (Filter.Eventually.exists hfalse).choose_spec

/-- A dense injective linear image of polynomials has a Hilbert basis
whose vectors are still in that image. -/
theorem hilbertBasis_in_polynomial_range {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : Polynomial ℂ →ₗ[ℂ] H) (hT : Function.Injective T)
    (hd : T.range.topologicalClosure = ⊤) :
    ∃ b : HilbertBasis ℕ ℂ H, ∀ n, b n ∈ LinearMap.range T := by
  let v : ℕ → H := T ∘ Polynomial.basisMonomials ℂ
  have hi : LinearIndependent ℂ v :=
    (Polynomial.basisMonomials ℂ).linearIndependent.map' T (LinearMap.ker_eq_bot.mpr hT)
  have hspan : Submodule.span ℂ (range v) = LinearMap.range T := by
    rw [show range v = T '' range (Polynomial.basisMonomials ℂ) from Set.range_comp _ _,
      ← Submodule.map_span, (Polynomial.basisMonomials ℂ).span_eq, Submodule.map_top]
  have hg := InnerProductSpace.gramSchmidtNormed_orthonormal (𝕜 := ℂ) hi
  have hd' : (Submodule.span ℂ (range (InnerProductSpace.gramSchmidtNormed ℂ v))).topologicalClosure = ⊤ := by
    rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt, hspan, hd]
  let b := HilbertBasis.mk hg hd'.ge
  refine ⟨b, ?_⟩
  intro n
  change HilbertBasis.mk hg hd'.ge n ∈ LinearMap.range T
  rw [HilbertBasis.coe_mk]
  rw [← hspan]
  exact Submodule.smul_mem _ _ (Submodule.span_mono (Set.image_subset_range _ _)
    (InnerProductSpace.gramSchmidt_mem_span ℂ v (i := n) (j := n) le_rfl))

/-- Polynomial density supplies the basis needed by the analytic construction. -/
theorem polynomial_hilbertBasis_of_dense [NeZero μ] (hμ : μ ≪ volume)
    (hm : ∀ p : Polynomial ℂ, MemLp (fun z => p.eval z) 2 μ)
    (hd : (polynomialL2 hm).range.topologicalClosure = ⊤) :
    ∃ (b : HilbertBasis ℕ ℂ (L2 μ)) (p : ℕ → Polynomial ℂ),
      ∀ n, (b n : ℂ → ℂ) =ᵐ[μ] (fun z => (p n).eval z) := by
  obtain ⟨b,hb⟩ := hilbertBasis_in_polynomial_range (polynomialL2 hm)
    (polynomialL2_injective hμ hm) hd
  have hb' : ∀ n, ∃ p, polynomialL2 hm p = b n := hb
  choose p hp using hb'
  refine ⟨b,p,?_⟩
  intro n
  rw [← hp n]
  exact polynomialL2_coeFn hm (p n)

/-- Proposition 4.1 with precisely the polynomial-density obligation exposed. -/
theorem exists_rigid_of_polynomial_density [NeZero μ] (hμ : μ ≪ volume)
    (hm : ∀ p : Polynomial ℂ, MemLp (fun z => p.eval z) 2 μ)
    (hd : (polynomialL2 hm).range.topologicalClosure = ⊤) :
    ∃ C : L2 μ →L[ℂ] L2 μ, C.IsPositive ∧ ‖C‖ ≤ (1:ℝ)/8 ∧
      IsCompactOperator C ∧ Function.Injective C ∧ ModulusRigid C := by
  obtain ⟨b,p,hp⟩ := polynomial_hilbertBasis_of_dense hμ hm hd
  exact exists_rigid_of_polynomial_basis hμ b p hp

end OperatorPhaseRetrieval

end
