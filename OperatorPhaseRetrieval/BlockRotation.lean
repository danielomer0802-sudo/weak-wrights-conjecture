import OperatorPhaseRetrieval.L2
import OperatorPhaseRetrieval.Projection

noncomputable section

open MeasureTheory Filter

/-! Explicit bounded block operators on the genuine Hilbert direct sum. -/

open scoped InnerProductSpace
namespace OperatorPhaseRetrieval
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev SumL2 (H : Type*) := WithLp 2 (H × H)

def pairL2 (a b : H) : SumL2 H := (WithLp.equiv 2 (H × H)).symm (a,b)
omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp] theorem pairL2_fst (a b : H) : (pairL2 a b).fst = a := rfl
omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp] theorem pairL2_snd (a b : H) : (pairL2 a b).snd = b := rfl

def firstL2 : SumL2 H →L[ℂ] H :=
  ContinuousLinearMap.fst ℂ H H ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toContinuousLinearMap
def secondL2 : SumL2 H →L[ℂ] H :=
  ContinuousLinearMap.snd ℂ H H ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toContinuousLinearMap

def blockRotation (C D : H →L[ℂ] H) : SumL2 H →L[ℂ] SumL2 H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap ∘L
    ((C ∘L firstL2 - D ∘L secondL2).prod
      (D ∘L firstL2 + C ∘L secondL2))

omit [CompleteSpace H] in
@[simp] theorem block_fst (C D : H →L[ℂ] H) (x : SumL2 H) :
    (blockRotation C D x).fst = C x.fst - D x.snd := rfl

omit [CompleteSpace H] in
@[simp] theorem block_snd (C D : H →L[ℂ] H) (x : SumL2 H) :
    (blockRotation C D x).snd = D x.fst + C x.snd := rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem sum_ext {x y : SumL2 H} (h₁ : x.fst=y.fst) (h₂ : x.snd=y.snd) : x=y := by
  apply (WithLp.equiv 2 (H × H)).injective
  exact Prod.ext h₁ h₂

theorem block_adjoint (C D : H →L[ℂ] H) (hC : IsSelfAdjoint C)
    (hD : IsSelfAdjoint D) : star (blockRotation C D) = blockRotation C (-D) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  have hc (u v : H) : inner (𝕜 := ℂ) (C u) v = inner (𝕜 := ℂ) u (C v) := hC.isSymmetric u v
  have hd (u v : H) : inner (𝕜 := ℂ) (D u) v = inner (𝕜 := ℂ) u (D v) := hD.isSymmetric u v
  simp only [WithLp.prod_inner_apply]
  change inner (𝕜 := ℂ) (blockRotation C (-D) x).fst y.fst +
    inner (𝕜 := ℂ) (blockRotation C (-D) x).snd y.snd =
    inner (𝕜 := ℂ) x.fst (blockRotation C D y).fst +
    inner (𝕜 := ℂ) x.snd (blockRotation C D y).snd
  simp only [block_fst, block_snd,
    neg_apply, sub_neg_eq_add,
    inner_add_left, inner_neg_left, inner_add_right, inner_sub_right,
    hc, hd]
  ring

omit [CompleteSpace H] in
theorem block_inverse_left (C D : H →L[ℂ] H)
    (hcomm : Commute C D) (hsq : C*C+D*D=1) :
    blockRotation C (-D) * blockRotation C D = 1 := by
  ext x : 1
  apply sum_ext
  · have hs := congrArg (fun T : H →L[ℂ] H => T x.fst) hsq
    have hc := congrArg (fun T : H →L[ℂ] H => T x.snd) hcomm.eq
    simp only [add_apply, mul_apply_eq_comp,
      one_apply_eq_self] at hs hc
    simp only [mul_apply_eq_comp, one_apply_eq_self,
      block_fst, block_snd, neg_apply,
      map_sub, map_add]
    calc
      _ = C (C x.fst) + D (D x.fst) := by rw [hc]; module
      _ = x.fst := hs
  · have hs := congrArg (fun T : H →L[ℂ] H => T x.snd) hsq
    have hc := congrArg (fun T : H →L[ℂ] H => T x.fst) hcomm.eq
    simp only [add_apply, mul_apply_eq_comp,
      one_apply_eq_self] at hs hc
    simp only [mul_apply_eq_comp, one_apply_eq_self,
      block_fst, block_snd, neg_apply,
      map_sub, map_add, sub_neg_eq_add]
    calc
      _ = C (C x.snd) + D (D x.snd) := by rw [hc]; module
      _ = x.snd := hs

theorem block_unitary (C D : H →L[ℂ] H) (hC : IsSelfAdjoint C)
    (hD : IsSelfAdjoint D) (hcomm : Commute C D) (hsq : C*C+D*D=1) :
    IsUnitary (blockRotation C D) := by
  rw [IsUnitary, block_adjoint C D hC hD]
  refine ⟨block_inverse_left C D hcomm hsq, ?_⟩
  have hc : Commute C (-D) := by
    show C * -D = -D * C
    simp only [mul_neg, neg_mul, hcomm.eq]
  have hs : C*C+(-D)*(-D)=1 := by simpa using hsq
  simpa only [neg_neg] using block_inverse_left C (-D) hc hs

def secondProjection : SumL2 H →L[ℂ] SumL2 H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap ∘L
    ((0 : SumL2 H →L[ℂ] H).prod secondL2)

omit [CompleteSpace H] in
@[simp] theorem second_fst (x : SumL2 H) : (secondProjection x).fst = 0 := rfl
omit [CompleteSpace H] in
@[simp] theorem second_snd (x : SumL2 H) : (secondProjection x).snd = x.snd := rfl

theorem second_isProjection : IsOrthogonalProjection (secondProjection (H := H)) := by
  constructor
  · ext x : 1
    apply sum_ext <;> simp [mul_apply_eq_comp]
  · symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro x y
    simp only [WithLp.prod_inner_apply]
    change inner (𝕜 := ℂ) (secondProjection x).fst y.fst +
      inner (𝕜 := ℂ) (secondProjection x).snd y.snd =
      inner (𝕜 := ℂ) x.fst (secondProjection y).fst +
      inner (𝕜 := ℂ) x.snd (secondProjection y).snd
    simp only [second_fst, second_snd, inner_zero_left,
      inner_zero_right, zero_add]

def blockProjection (C D : H →L[ℂ] H) : SumL2 H →L[ℂ] SumL2 H :=
  blockRotation C D * secondProjection * star (blockRotation C D)

theorem blockProjection_isProjection (C D : H →L[ℂ] H)
    (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D)
    (hcomm : Commute C D) (hsq : C*C+D*D=1) :
    IsOrthogonalProjection (blockProjection C D) :=
  conjugate_projection _ _ second_isProjection (block_unitary C D hC hD hcomm hsq)

theorem block_measurement (C D : H →L[ℂ] H)
    (hC : IsSelfAdjoint C) (hD : IsSelfAdjoint D)
    (hcomm : Commute C D) (hsq : C*C+D*D=1) (η : ℂ) (x : SumL2 H) :
    phaseFamily (blockProjection C D) η (blockRotation C D x) =
      pairL2 (C x.fst - η • D x.snd) (D x.fst + η • C x.snd) := by
  have hV := block_unitary C D hC hD hcomm hsq
  have hinv : star (blockRotation C D) (blockRotation C D x) = x :=
    congrArg (fun T : SumL2 H →L[ℂ] SumL2 H => T x) hV.1
  rw [blockProjection, conjugate_phaseFamily _ _ hV]
  simp only [mul_apply_eq_comp, hinv]
  apply sum_ext
  · simp [phaseFamily, add_apply, smul_apply,
      WithLp.add_fst, WithLp.smul_fst, map_add, map_smul]
    module
  · simp [phaseFamily, add_apply, smul_apply,
      WithLp.add_snd, WithLp.smul_snd,
      map_add, map_smul]
    module

end OperatorPhaseRetrieval

end
