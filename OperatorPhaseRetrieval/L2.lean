import OperatorPhaseRetrieval.ThreePhase

noncomputable section

/-! Concrete a.e. bookkeeping on Mathlib's `Lp ℂ 2 μ`, not a custom signal model. -/

open MeasureTheory Filter
namespace OperatorPhaseRetrieval

abbrev L2 {X : Type*} [MeasurableSpace X] (μ : Measure X) := Lp ℂ 2 μ

def PhaseRelated {H : Type*} [SMul ℂ H] (f g : H) : Prop :=
  ∃ ω : ℂ, IsPhase ω ∧ g = ω • f

theorem phaseRelated_refl {H : Type*} [MulAction ℂ H] (f : H) : PhaseRelated f f :=
  ⟨1, norm_one, (one_smul ℂ f).symm⟩

theorem phase_ne_zero {ω : ℂ} (h : IsPhase ω) : ω ≠ 0 := by
  intro he
  simp [IsPhase, he] at h

theorem phaseRelated_zero_iff {H : Type*} [AddCommGroup H] [Module ℂ H]
    {f : H} : PhaseRelated f 0 ↔ f = 0 := by
  constructor
  · rintro ⟨ω, hω, he⟩
    exact (smul_eq_zero.mp he.symm).resolve_left (phase_ne_zero hω)
  · rintro rfl
    exact phaseRelated_refl 0

section Measure
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def ModEq (f g : L2 μ) : Prop := ∀ᵐ t ∂μ, ‖f t‖ = ‖g t‖

/-- The exact positive-measure modulus-rigidity property in Proposition 4.1. -/
def ModulusRigid (C : L2 μ →L[ℂ] L2 μ) : Prop :=
  ∀ f g, 0 < μ {t | ‖C f t‖ = ‖C g t‖} → PhaseRelated f g

theorem norm_eq_of_modEq {f g : L2 μ} (h : ModEq f g) : ‖f‖ = ‖g‖ := by
  apply le_antisymm
  · exact Lp.norm_le_norm_of_ae_le (h.mono fun _ he => he.le)
  · exact Lp.norm_le_norm_of_ae_le (h.mono fun _ he => he.ge)

theorem modEq_smul (f : L2 μ) {ω : ℂ} (hω : IsPhase ω) : ModEq f (ω • f) := by
  filter_upwards [Lp.coeFn_smul ω f] with t ht
  rw [ht]
  simp [show ‖ω‖=1 from hω]

theorem modEq_of_phaseRelated {f g : L2 μ} (h : PhaseRelated f g) : ModEq f g := by
  rcases h with ⟨ω, hω, rfl⟩
  exact modEq_smul f hω

theorem phaseRelated_map (T : L2 μ →L[ℂ] L2 μ) {f g : L2 μ}
    (h : PhaseRelated f g) : PhaseRelated (T f) (T g) := by
  rcases h with ⟨ω, hω, rfl⟩
  exact ⟨ω, hω, T.map_smul ω f⟩

theorem rigid_separated {C : L2 μ →L[ℂ] L2 μ} (hC : ModulusRigid C)
    {f g : L2 μ} (hfg : ¬ PhaseRelated f g) :
    ∀ᵐ t ∂μ, ‖C f t‖ ≠ ‖C g t‖ := by
  apply ae_iff.mpr
  simp only [not_not]
  by_contra hn
  exact hfg (hC f g (bot_lt_iff_ne_bot.mpr hn))

theorem rigid_global [NeZero μ] {C : L2 μ →L[ℂ] L2 μ}
    (hC : ModulusRigid C) {f g : L2 μ} (h : ModEq (C f) (C g)) :
    PhaseRelated f g := by
  by_contra hn
  have hc := h.and (rigid_separated hC hn)
  obtain ⟨t, ht, hnt⟩ := hc.exists
  exact hnt ht

theorem rigid_nonzero_ae {C : L2 μ →L[ℂ] L2 μ}
    (hC : ModulusRigid C) {f : L2 μ} (hf : f ≠ 0) :
    ∀ᵐ t ∂μ, C f t ≠ 0 := by
  have hs := rigid_separated hC (fun h => hf (phaseRelated_zero_iff.mp h))
  filter_upwards [hs, Lp.coeFn_zero ℂ 2 μ] with t ht hz
  intro he
  apply ht
  rw [map_zero, hz, he]
  rfl

theorem rigid_injective [NeZero μ] {C : L2 μ →L[ℂ] L2 μ}
    (hC : ModulusRigid C) : Function.Injective C := by
  have hker : ∀ f, C f = 0 → f = 0 := by
    intro f hf
    apply phaseRelated_zero_iff.mp
    apply rigid_global hC
    unfold ModEq
    simp [hf]
  intro f g he
  apply sub_eq_zero.mp
  apply hker
  simp [map_sub, he]

theorem ae_smul_map (T : L2 μ →L[ℂ] L2 μ) (ω : ℂ) (f : L2 μ) :
    ∀ᵐ t ∂μ, T (ω • f) t = ω * T f t := by
  rw [T.map_smul]
  exact Lp.coeFn_smul ω (T f)

theorem nonzero_support_exists {f : L2 μ} (hf : f ≠ 0)
    {p : X → Prop} (hp : ∀ᵐ t ∂μ, p t) : ∃ t, p t ∧ f t ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hf
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hp] with t ht
  exact hn t ht

end Measure

/-- The conjugate in this identity is essential: it forces the phases to agree. -/
theorem synchronize_phases {α β u v : ℂ} (hβ : IsPhase β)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (he : u * star v = (α*u) * star (β*v)) : α = β := by
  have hp : u * star v ≠ 0 := mul_ne_zero hu (by simpa using hv)
  have hq : 1-α*star β = 0 := by
    apply (mul_eq_zero.mp (show (1-α*star β)*(u*star v)=0 by
      simp only [star_mul] at he
      linear_combination he)).resolve_right hp
  have hb := phase_mul_conj hβ
  linear_combination -β*hq - α*hb

end OperatorPhaseRetrieval

end
