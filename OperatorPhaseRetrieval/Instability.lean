import OperatorPhaseRetrieval.DiagonalSmoothing

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped Topology

/-! # Quantitative instability of the block construction -/
open MeasureTheory Filter
open scoped Topology
namespace OperatorPhaseRetrieval
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def magnitude (f : L2 μ) : Lp ℝ 2 μ :=
  lipschitzWith_one_norm.compLp (norm_zero : ‖(0:ℂ)‖ = 0) f

theorem magnitude_coeFn (f : L2 μ) :
    (magnitude f : X → ℝ) =ᵐ[μ] (fun z => ‖f z‖) :=
  lipschitzWith_one_norm.coeFn_compLp norm_zero f

theorem magnitude_neg (f : L2 μ) : magnitude (-f) = magnitude f := by
  apply Lp.ext
  filter_upwards [magnitude_coeFn (-f), magnitude_coeFn f, Lp.coeFn_neg f] with z h₁ h₂ h₃
  simp only [h₁,h₂,h₃,Pi.neg_apply,norm_neg]

theorem magnitude_sub_le (f g : L2 μ) : ‖magnitude f - magnitude g‖ ≤ ‖f-g‖ := by
  simpa [magnitude] using lipschitzWith_one_norm.norm_compLp_sub_le
    (norm_zero : ‖(0:ℂ)‖ = 0) f g

theorem magnitude_add_sub_le_left (a b : L2 μ) :
    ‖magnitude (a+b) - magnitude (a-b)‖ ≤ 2 * ‖a‖ := by
  rw [← magnitude_neg (a-b)]
  have h := magnitude_sub_le (a+b) (-(a-b))
  have he : (a+b) - (-(a-b)) = (2:ℂ) • a := by module
  simpa only [he, norm_smul, Complex.norm_ofNat] using h

theorem magnitude_add_sub_le_right (a b : L2 μ) :
    ‖magnitude (a+b) - magnitude (a-b)‖ ≤ 2 * ‖b‖ := by
  have h := magnitude_sub_le (a+b) (a-b)
  have he : (a+b) - (a-b) = (2:ℂ) • b := by module
  simpa only [he, norm_smul, Complex.norm_ofNat] using h

def pairMagnitude (x : SumL2 (L2 μ)) : WithLp 2 (Lp ℝ 2 μ × Lp ℝ 2 μ) :=
  pairL2 (magnitude x.fst) (magnitude x.snd)

variable (C D : L2 μ →L[ℂ] L2 μ)

def unstablePlus (u : L2 μ) : SumL2 (L2 μ) := blockRotation C D (pairL2 u u)
def unstableMinus (u : L2 μ) : SumL2 (L2 μ) := blockRotation C D (pairL2 u (-u))

theorem unstable_norm_sq (hV : IsUnitary (blockRotation C D)) (u : L2 μ) :
    ‖unstablePlus C D u‖^2 = 2*‖u‖^2 ∧ ‖unstableMinus C D u‖^2 = 2*‖u‖^2 := by
  simp only [unstablePlus, unstableMinus, unitary_norm _ hV,
    WithLp.prod_norm_sq_eq_of_L2, pairL2_fst, pairL2_snd, norm_neg]
  constructor <;> ring

/-- Every phase leaves the two input vectors a fixed distance apart. -/
theorem unstable_separation_sq (hV : IsUnitary (blockRotation C D))
    (u : L2 μ) {ω : ℂ} (hω : IsPhase ω) :
    ‖unstablePlus C D u - ω • unstableMinus C D u‖^2 = 4*‖u‖^2 := by
  have he : unstablePlus C D u - ω • unstableMinus C D u =
      blockRotation C D (pairL2 ((1-ω) • u) ((1+ω) • u)) := by
    unfold unstablePlus unstableMinus
    rw [← map_smul, ← map_sub]
    congr 1
    apply sum_ext <;> simp [WithLp.sub_fst, WithLp.sub_snd,
      WithLp.smul_fst, WithLp.smul_snd] <;> module
  rw [he, unitary_norm _ hV, WithLp.prod_norm_sq_eq_of_L2,
    pairL2_fst, pairL2_snd, norm_smul, norm_smul]
  have ha := norm_add_sq (𝕜 := ℂ) (1:ℂ) ω
  have hs := norm_sub_sq (𝕜 := ℂ) (1:ℂ) ω
  have hn : ‖1-ω‖^2 + ‖1+ω‖^2 = 4 := by
    rw [norm_one, show ‖ω‖ = 1 from hω] at ha hs
    linarith
  nlinarith [sq_nonneg ‖u‖]

/-- The data approach each other uniformly in the unimodular phase. -/
theorem unstable_data_bound_sq (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D)
    (hcomm : Commute C D) (hsq : C*C+D*D=1) (u : L2 μ) {η : ℂ} (hη : IsPhase η) :
    ‖pairMagnitude (phaseFamily (blockProjection C D) η (unstablePlus C D u)) -
      pairMagnitude (phaseFamily (blockProjection C D) η (unstableMinus C D u))‖^2
      ≤ 8 * ‖C u‖^2 := by
  rw [unstablePlus, unstableMinus, block_measurement C D hC hD hcomm hsq,
    block_measurement C D hC hD hcomm hsq]
  simp only [pairL2_fst,pairL2_snd,map_neg,smul_neg,sub_neg_eq_add,← sub_eq_add_neg]
  have h₁ : ‖magnitude (C u - η • D u) - magnitude (C u + η • D u)‖ ≤ 2*‖C u‖ := by
    rw [norm_sub_rev]
    exact magnitude_add_sub_le_left _ _
  have h₂ := magnitude_add_sub_le_right (D u) (η • C u)
  rw [norm_smul, show ‖η‖ = 1 from hη, one_mul] at h₂
  simp only [pairMagnitude, WithLp.prod_norm_sq_eq_of_L2, WithLp.sub_fst,
    WithLp.sub_snd, pairL2_fst, pairL2_snd]
  nlinarith [norm_nonneg (magnitude (C u - η • D u) - magnitude (C u + η • D u)),
    norm_nonneg (magnitude (D u + η • C u) - magnitude (D u - η • C u)), norm_nonneg (C u)]

def halfNormBasisVector (b : HilbertBasis ℕ ℂ (L2 μ)) (n : ℕ) : L2 μ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • b n

theorem halfNormBasisVector_norm_sq (b : HilbertBasis ℕ ℂ (L2 μ)) (n : ℕ) :
    ‖halfNormBasisVector b n‖^2 = (1:ℝ)/2 := by
  rw [halfNormBasisVector, norm_smul, b.orthonormal.norm_eq_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem halfNormBasisVector_diagonal_norm_sq (b : HilbertBasis ℕ ℂ (L2 μ))
    {w : ℕ → ℝ} (hw : Summable w) (n : ℕ) :
    ‖diagonalSmoothing b w (halfNormBasisVector b n)‖^2 = (w n)^2/2 := by
  have he : diagonalSmoothing b w (halfNormBasisVector b n) =
      (w n : ℂ) • halfNormBasisVector b n := by
    rw [halfNormBasisVector, map_smul, diagonalSmoothing_basis b hw]
    exact smul_comm _ _ _
  rw [he, norm_smul, mul_pow, halfNormBasisVector_norm_sq,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- Unit input vectors separated by sqrt(2), whose magnitude data have
distance at most 2 |w_n| for every phase. -/
theorem unstable_unit_vectors (b : HilbertBasis ℕ ℂ (L2 μ)) {w : ℕ → ℝ}
    (hw : Summable w) (hD : IsSelfAdjoint D)
    (hcomm : Commute (diagonalSmoothing b w) D)
    (hsq : diagonalSmoothing b w * diagonalSmoothing b w + D*D = 1) (n : ℕ) :
    ∃ x y : SumL2 (L2 μ), ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      (∀ ω : ℂ, IsPhase ω → ‖x - ω • y‖ = Real.sqrt 2) ∧
      ∀ η : ℂ, IsPhase η →
        ‖pairMagnitude (phaseFamily (blockProjection (diagonalSmoothing b w) D) η x) -
          pairMagnitude (phaseFamily (blockProjection (diagonalSmoothing b w) D) η y)‖ ≤ 2*|w n| := by
  let C := diagonalSmoothing b w
  let u := halfNormBasisVector b n
  let x := unstablePlus C D u
  let y := unstableMinus C D u
  have hC := diagonalSmoothing_selfAdjoint b hw
  have hV := block_unitary C D hC hD hcomm hsq
  have hu : ‖u‖^2 = (1:ℝ)/2 := halfNormBasisVector_norm_sq b n
  have hnorm := unstable_norm_sq C D hV u
  refine ⟨x,y, ?_, ?_, ?_, ?_⟩
  · change ‖unstablePlus C D u‖ = 1
    nlinarith [hnorm.1, norm_nonneg (unstablePlus C D u)]
  · change ‖unstableMinus C D u‖ = 1
    nlinarith [hnorm.2, norm_nonneg (unstableMinus C D u)]
  · intro ω hω
    have he := unstable_separation_sq C D hV u hω
    change ‖unstablePlus C D u - ω • unstableMinus C D u‖ = Real.sqrt 2
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2,
      norm_nonneg (unstablePlus C D u - ω • unstableMinus C D u)]
  · intro η hη
    have he := unstable_data_bound_sq C D hC hD hcomm hsq u hη
    have hn : ‖C u‖^2 = (w n)^2/2 := halfNormBasisVector_diagonal_norm_sq b hw n
    change ‖pairMagnitude (phaseFamily (blockProjection C D) η (unstablePlus C D u)) -
      pairMagnitude (phaseFamily (blockProjection C D) η (unstableMinus C D u))‖ ≤ 2*|w n|
    nlinarith [sq_abs (w n), abs_nonneg (w n)]

/-- Uniform recovery on the unit sphere, stated directly modulo phase.
The data use the maximum of finitely many component distances, equivalently
the usual finite product norm. -/
def UniformPhaseRecovery {ι : Type*} (T : ι → SumL2 (L2 μ) →L[ℂ] SumL2 (L2 μ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : SumL2 (L2 μ), ‖x‖ = 1 → ‖y‖ = 1 →
      (∀ j, ‖pairMagnitude (T j x) - pairMagnitude (T j y)‖ < δ) →
      ∃ ω : ℂ, IsPhase ω ∧ ‖x - ω • y‖ < ε

/-- Remark 6.3: the diagonal block construction has no uniformly continuous
inverse modulo phase on the unit sphere, for any fixed finite phase family.
The proof even rules out the displayed uniform criterion for arbitrary families. -/
theorem diagonal_no_uniform_phase_recovery {ι : Type*}
    (b : HilbertBasis ℕ ℂ (L2 μ)) {w : ℕ → ℝ} (hw : Summable w)
    (hD : IsSelfAdjoint D) (hcomm : Commute (diagonalSmoothing b w) D)
    (hsq : diagonalSmoothing b w * diagonalSmoothing b w + D*D = 1)
    (η : ι → ℂ) (hη : ∀ j, IsPhase (η j)) :
    ¬ UniformPhaseRecovery (fun j => phaseFamily (blockProjection (diagonalSmoothing b w) D) (η j)) := by
  intro h
  obtain ⟨δ,hδ,hh⟩ := h 1 zero_lt_one
  have ht : Tendsto (fun n => 2*|w n|) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hw.tendsto_atTop_zero.abs
  obtain ⟨n,hn⟩ := (ht.eventually_lt_const hδ).exists
  obtain ⟨x,y,hx,hy,hsep,hdata⟩ := unstable_unit_vectors D b hw hD hcomm hsq n
  obtain ⟨ω,hω,hclose⟩ := hh x y hx hy (fun j => (hdata (η j) (hη j)).trans_lt hn)
  rw [hsep ω hω] at hclose
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

end OperatorPhaseRetrieval

end
