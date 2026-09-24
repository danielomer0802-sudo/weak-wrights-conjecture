import OperatorPhaseRetrieval.BlockRotation

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped Topology

/-! Spatial L2 equivalences from measurable inverse maps modulo null sets. -/
open MeasureTheory
namespace OperatorPhaseRetrieval
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

theorem l2_ae_pullback_inverse (τ : X → Y) (σ : Y → X)
    (hτ : MeasurePreserving τ μ ν) (hσ : MeasurePreserving σ ν μ)
    (hστ : (fun x => σ (τ x)) =ᵐ[μ] id) (f : L2 μ) :
    Lp.compMeasurePreserving τ hτ (Lp.compMeasurePreserving σ hσ f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving σ hσ f) hτ,
    hτ.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hσ), hστ] with x hx hy hz
  exact hx.trans (hy.trans (congrArg f hz))

def aeSpatialPullback (τ : X → Y) (σ : Y → X)
    (hτ : MeasurePreserving τ μ ν) (hσ : MeasurePreserving σ ν μ)
    (hστ : (fun x => σ (τ x)) =ᵐ[μ] id)
    (hτσ : (fun y => τ (σ y)) =ᵐ[ν] id) : L2 ν ≃ₗᵢ[ℂ] L2 μ :=
  LinearIsometryEquiv.ofLinearIsometry (Lp.compMeasurePreservingₗᵢ ℂ τ hτ)
    (Lp.compMeasurePreservingₗ ℂ σ hσ)
    (by ext f : 1; exact l2_ae_pullback_inverse τ σ hτ hσ hστ f)
    (by ext f : 1; exact l2_ae_pullback_inverse σ τ hσ hτ hτσ f)

theorem pullback_modEq_forward (τ : X → Y) (hτ : MeasurePreserving τ μ ν)
    {f g : L2 ν} (h : ModEq f g) :
    ModEq (Lp.compMeasurePreserving τ hτ f) (Lp.compMeasurePreserving τ hτ g) := by
  filter_upwards [hτ.quasiMeasurePreserving.ae h,
    Lp.coeFn_compMeasurePreserving f hτ, Lp.coeFn_compMeasurePreserving g hτ] with x hx hf hg
  rw [hf,hg]
  exact hx

theorem aeSpatialPullback_modEq (τ : X → Y) (σ : Y → X)
    (hτ : MeasurePreserving τ μ ν) (hσ : MeasurePreserving σ ν μ)
    (hστ : (fun x => σ (τ x)) =ᵐ[μ] id)
    (hτσ : (fun y => τ (σ y)) =ᵐ[ν] id) (f g : L2 ν) :
    ModEq (aeSpatialPullback τ σ hτ hσ hστ hτσ f)
      (aeSpatialPullback τ σ hτ hσ hστ hτσ g) ↔ ModEq f g := by
  constructor
  · intro h
    have hi := pullback_modEq_forward σ hσ h
    change ModEq
      (Lp.compMeasurePreserving σ hσ (Lp.compMeasurePreserving τ hτ f))
      (Lp.compMeasurePreserving σ hσ (Lp.compMeasurePreserving τ hτ g)) at hi
    rwa [l2_ae_pullback_inverse σ τ hσ hτ hτσ f,
      l2_ae_pullback_inverse σ τ hσ hτ hτσ g] at hi
  · exact pullback_modEq_forward τ hτ

end OperatorPhaseRetrieval

end
