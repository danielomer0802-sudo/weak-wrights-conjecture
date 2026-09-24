import OperatorPhaseRetrieval.SpatialTransfer

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace
open MeasureTheory
open scoped CStarAlgebra
open Set Filter
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped Topology

/-! # Actual L2 pullback by a measure-preserving measurable equivalence

This proves the pullback part of spatial transfer. It does not assert the
classification theorem for atomless standard probability spaces.
-/
open MeasureTheory
namespace OperatorPhaseRetrieval
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

theorem l2_pullback_inverse (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (f : L2 μ) :
    Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm (he.symm e) f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (Lp.compMeasurePreserving e.symm (he.symm e) f) he,
    he.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f (he.symm e))] with x hx hy
  exact hx.trans (hy.trans (by simp))

/-- Pullback has a proved inverse and hence is a linear isometry equivalence. -/
def spatialPullback (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) :
    L2 ν ≃ₗᵢ[ℂ] L2 μ :=
  LinearIsometryEquiv.ofLinearIsometry (Lp.compMeasurePreservingₗᵢ ℂ e he)
    (Lp.compMeasurePreservingₗ ℂ e.symm (he.symm e))
    (by ext f : 1; exact l2_pullback_inverse e he f)
    (by ext f : 1; exact l2_pullback_inverse e.symm (he.symm e) f)

theorem spatialPullback_coeFn (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) (f : L2 ν) :
    (spatialPullback e he f : X → ℂ) =ᵐ[μ] fun x => f (e x) :=
  Lp.coeFn_compMeasurePreserving f he

theorem spatialPullback_modEq_forward (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    {f g : L2 ν} (h : ModEq f g) :
    ModEq (spatialPullback e he f) (spatialPullback e he g) := by
  filter_upwards [he.quasiMeasurePreserving.ae h,
    spatialPullback_coeFn e he f, spatialPullback_coeFn e he g] with x hx hf hg
  rw [hf,hg]
  exact hx

theorem spatialPullback_modEq (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (f g : L2 ν) : ModEq (spatialPullback e he f) (spatialPullback e he g) ↔ ModEq f g := by
  constructor
  · intro h
    have hi := spatialPullback_modEq_forward e.symm (he.symm e) h
    change ModEq (Lp.compMeasurePreserving e.symm (he.symm e) (Lp.compMeasurePreserving e he f))
      (Lp.compMeasurePreserving e.symm (he.symm e) (Lp.compMeasurePreserving e he g)) at hi
    have hf : Lp.compMeasurePreserving e.symm (he.symm e)
        (Lp.compMeasurePreserving e he f) = f := l2_pullback_inverse e.symm (he.symm e) f
    have hg : Lp.compMeasurePreserving e.symm (he.symm e)
        (Lp.compMeasurePreserving e he g) = g := l2_pullback_inverse e.symm (he.symm e) g
    rwa [hf,hg] at hi
  · exact spatialPullback_modEq_forward e he

/-- Phase-retrieval projections transport along an actual measurable
measure-preserving equivalence. -/
theorem projectionWorks_of_measureEquiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (h : ProjectionWorks (@ModEq X _ μ)) : ProjectionWorks (@ModEq Y _ ν) :=
  transfer_projectionWorks (spatialPullback e he) (spatialPullback_modEq e he) h

end OperatorPhaseRetrieval

end
