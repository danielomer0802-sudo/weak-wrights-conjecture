import OperatorPhaseRetrieval.CompactModel
import OperatorPhaseRetrieval.GapApproximation

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

/-! Polynomial density on the positive-area product, using Stone--Weierstrass. -/
open Set
namespace OperatorPhaseRetrieval
variable (K : Set ℂ) [CompactSpace K]

/-- The elements of the polynomial closure whose conjugates also belong to it. -/
def polynomialStarCore : StarSubalgebra ℂ C(K,ℂ) where
  carrier := {f | f ∈ uniformPolynomialClosure K ∧ star f ∈ uniformPolynomialClosure K}
  zero_mem' := ⟨(uniformPolynomialClosure K).zero_mem, by simp⟩
  one_mem' := ⟨(uniformPolynomialClosure K).one_mem, by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨(uniformPolynomialClosure K).add_mem hf.1 hg.1,
      by simpa using (uniformPolynomialClosure K).add_mem hf.2 hg.2⟩
  mul_mem' := by
    intro f g hf hg
    exact ⟨(uniformPolynomialClosure K).mul_mem hf.1 hg.1,
      by simpa using (uniformPolynomialClosure K).mul_mem hf.2 hg.2⟩
  algebraMap_mem' := by
    intro c
    exact ⟨(uniformPolynomialClosure K).algebraMap_mem c,
      by simpa only [algebraMap_star_comm] using (uniformPolynomialClosure K).algebraMap_mem (star c)⟩
  star_mem' := by
    intro f hf
    exact ⟨hf.2, by simpa using hf.1⟩

theorem realCut_mem_starCore [Nonempty K] (hK : IsPreconnected Kᶜ) (f : C(K,ℂ))
    (hfm : f ∈ uniformPolynomialClosure K) (hf : ∀ z, (f z).re ≠ 0) :
    realCut K f hf ∈ polynomialStarCore K := by
  have hm := realCut_mem_uniformClosure K hK f hfm hf
  refine ⟨hm, ?_⟩
  have he : star (realCut K f hf) = realCut K f hf := by
    ext z
    simp only [ContinuousMap.star_apply, realCut_apply]
    split_ifs <;> simp
  rwa [he]

theorem uniformClosure_eq_top_of_real_cuts [Nonempty K]
    (hK : IsPreconnected Kᶜ)
    (hsep : ∀ x y : K, x ≠ y → ∃ f : C(K,ℂ),
      f ∈ uniformPolynomialClosure K ∧ (∀ z, (f z).re ≠ 0) ∧
      (f x).re < 0 ∧ 0 < (f y).re ∨
      f ∈ uniformPolynomialClosure K ∧ (∀ z, (f z).re ≠ 0) ∧
      (f y).re < 0 ∧ 0 < (f x).re) :
    uniformPolynomialClosure K = ⊤ := by
  have hs : (polynomialStarCore K).SeparatesPoints := by
    intro x y hxy
    obtain ⟨f,hf⟩ := hsep x y hxy
    rcases hf with ⟨hm,hn,hx,hy⟩ | ⟨hm,hn,hy,hx⟩
    · refine ⟨realCut K f hn, ⟨realCut K f hn, realCut_mem_starCore K hK f hm hn,rfl⟩, ?_⟩
      simp [realCut_apply, hx, not_lt.mpr hy.le]
    · refine ⟨realCut K f hn, ⟨realCut K f hn, realCut_mem_starCore K hK f hm hn,rfl⟩, ?_⟩
      simp [realCut_apply, hy, not_lt.mpr hx.le]
  have he := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (polynomialStarCore K) hs
  have hc : closure (polynomialStarCore K : Set C(K,ℂ)) ⊆
      (uniformPolynomialClosure K : Set C(K,ℂ)) :=
    closure_minimal (fun _ h => h.1) (uniformPolynomialClosure_closed K)
  apply top_unique
  intro f hf
  apply hc
  change f ∈ (polynomialStarCore K).topologicalClosure
  rw [he]
  trivial

theorem planarProduct_polynomialClosure {F : Set ℝ} (hFc : IsCompact F)
    (hFne : F.Nonempty) (hFq : ∀ q : ℚ, (q:ℝ) ∉ F) :
    letI : CompactSpace (planarProduct F) := isCompact_iff_compactSpace.mp (planarProduct_compact hFc)
    uniformPolynomialClosure (planarProduct F) = ⊤ := by
  let K := planarProduct F
  let : CompactSpace K := isCompact_iff_compactSpace.mp (planarProduct_compact hFc)
  let : Nonempty K := by
    obtain ⟨a,ha⟩ := hFne
    exact ⟨⟨⟨a,a⟩,ha,ha⟩⟩
  apply uniformClosure_eq_top_of_real_cuts K
    (planarProduct_complement_pathConnected (by simpa using hFq 0)).isConnected.isPreconnected
  intro x y hxy
  have mkcut (c : ℂ) (hc : ∀ z : K, ∀ q : ℚ, (c * (z:ℂ)).re ≠ (q:ℝ))
      (hne : (c * (x:ℂ)).re ≠ (c * (y:ℂ)).re) :
      ∃ f : C(K,ℂ),
        f ∈ uniformPolynomialClosure K ∧ (∀ z, (f z).re ≠ 0) ∧
        (f x).re < 0 ∧ 0 < (f y).re ∨
        f ∈ uniformPolynomialClosure K ∧ (∀ z, (f z).re ≠ 0) ∧
        (f y).re < 0 ∧ 0 < (f x).re := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    all_goals
      obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn hlt
      let f : C(K,ℂ) := c • coordinateMap K - ContinuousMap.const K (q:ℂ)
      have hm : f ∈ uniformPolynomialClosure K :=
        (uniformPolynomialClosure K).sub_mem
          ((uniformPolynomialClosure K).smul_mem (coordinateMap_mem K) c)
          ((uniformPolynomialClosure K).algebraMap_mem (q:ℂ))
      have hn : ∀ z, (f z).re ≠ 0 := by
        intro z
        change (c * (z:ℂ) - (q:ℂ)).re ≠ 0
        simpa using sub_ne_zero.mpr (hc z q)
      refine ⟨f, ?_⟩
    · left
      exact ⟨hm,hn,by simpa [f,coordinateMap] using sub_neg.mpr hq₁,
        by simpa [f,coordinateMap] using sub_pos.mpr hq₂⟩
    · right
      exact ⟨hm,hn,by simpa [f,coordinateMap] using sub_neg.mpr hq₁,
        by simpa [f,coordinateMap] using sub_pos.mpr hq₂⟩
  by_cases hr : (x:ℂ).re = (y:ℂ).re
  · apply mkcut (-Complex.I)
    · intro z q he
      have hz : (z:ℂ).im = (q:ℝ) := by simpa using he
      exact hFq q (hz ▸ z.property.2)
    · intro he
      have hi : (x:ℂ).im = (y:ℂ).im := by simpa using he
      exact hxy (Subtype.ext (Complex.ext hr hi))
  · apply mkcut 1
    · intro z q he
      have hz : (z:ℂ).re = (q:ℝ) := by simpa using he
      exact hFq q (hz ▸ z.property.1)
    · simpa using hr

end OperatorPhaseRetrieval

end
