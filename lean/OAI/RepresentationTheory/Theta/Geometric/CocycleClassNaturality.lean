import OAI.RepresentationTheory.Theta.Geometric.CocycleClassIndependence
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction
import OAI.AlgebraicTopology.Cohomology.Singular.Homotopy

/-! # Cocycle Class Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Continuous pullback preserves the constructed singular Chern class.
Homotopic maps therefore give the same class of the actual pulled cocycle. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicTopology.Cohomology.Singular.Homotopy
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback

variable {T Y Z : TopCat} {I : Type} (C : ContinuousLine.ContinuousLineCocycle T I)

theorem ContinuousLine.ContinuousLineCocycle.pullback_comp (f : Y ⟶ T) (g : Z ⟶ Y) :
    (C.pullback f).pullback g = C.pullback (g ≫ f) := rfl

theorem ContinuousLine.ContinuousLineCocycle.pullback_pointTransition (f : Y ⟶ T) (i j : I) (p : Y)
    (hi : p ∈ (C.pullback f).cover i) (hj : p ∈ (C.pullback f).cover j) :
    (C.pullback f).pointTransition i j p hi hj = C.pointTransition i j (f p) hi hj := rfl

variable [CompactSpace T] [NormalSpace T] [CompactSpace Y] [NormalSpace Y]

theorem ContinuousLine.ContinuousLineCocycle.chernClass_pullback (f : Y ⟶ T) :
    (C.pullback f).chernClass = AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 2 C.chernClass := by
  let V := AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover f C.logCover
  have hV := AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover_covers f C.logCover C.logCover_covers
  let l := AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.logarithmPullback f C.logCover C.logarithm
  have hl := AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.exponentialCocycle_pullback f C.logCover C.logarithm C.logarithm_cocycle
  have hr : ∀ i, V i ≤ (C.pullback f).cover (C.logParent i) :=
    fun i p hp => C.logCover_subset i hp
  have he : ∀ (a : Fin 2 → C.LogIndex) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a),
      Complex.exp (l a p) = (C.pullback f).pointTransition (C.logParent (a 0)) (C.logParent (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 1 p.property)) := by
    intro a p
    rw [ContinuousLine.ContinuousLineCocycle.pullback_pointTransition]
    exact (C.exp_logarithm a (AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.intersectionMap f C.logCover a p)).trans
      (C.transition_eq_point (C.logParent ∘ a) _)
  exact ((C.pullback f).chernClass_eq_on_cover V hV C.logParent hr l hl he).symm.trans
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.logarithmicSingularClass_pullback f C.logCover C.logCover_covers C.logarithm C.logarithm_cocycle)

theorem ContinuousLine.ContinuousLineCocycle.chernClass_pullback_homotopic (f g : Y ⟶ T) (h : f.hom.Homotopic g.hom) :
    (C.pullback f).chernClass = (C.pullback g).chernClass := by
  rw [ContinuousLine.ContinuousLineCocycle.chernClass_pullback, ContinuousLine.ContinuousLineCocycle.chernClass_pullback,
    AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyPullback_eq_of_homotopic (ModuleCat.of ℚ ℚ) h 2]

end

/-! Homotopic maps from a compact Hausdorff space pull an actual
transition cocycle back to the same Chern class. The target can be noncompact. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.TopologicalSpace

theorem ContinuousLine.ContinuousLineCocycle.chernClass_homotopic_compact_source
    {T Y : TopCat} {I : Type} (C : ContinuousLine.ContinuousLineCocycle T I)
    [CompactSpace Y] [T2Space Y] (f g : Y ⟶ T) (h : f.hom.Homotopic g.hom) :
    (C.pullback f).chernClass = (C.pullback g).chernClass := by
  obtain ⟨H⟩ := h
  let Z := TopCat.of (unitInterval × Y)
  let F : Z ⟶ T := TopCat.ofHom H.toContinuousMap
  let i₀ : Y ⟶ Z := TopCat.ofHom ⟨fun y => ((0 : unitInterval), y), continuous_const.prodMk continuous_id⟩
  let i₁ : Y ⟶ Z := TopCat.ofHom ⟨fun y => ((1 : unitInterval), y), continuous_const.prodMk continuous_id⟩
  have hi₀ : i₀ ≫ F = f := by
    apply TopCat.ext
    intro y
    exact H.map_zero_left y
  have hi₁ : i₁ ≫ F = g := by
    apply TopCat.ext
    intro y
    exact H.map_one_left y
  have hI : i₀.hom.Homotopic i₁.hom := ⟨{
    toFun := fun p => p
    continuous_toFun := continuous_id
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl }⟩
  have hc := (C.pullback F).chernClass_pullback_homotopic i₀ i₁ hI
  rw [ContinuousLine.ContinuousLineCocycle.pullback_comp, ContinuousLine.ContinuousLineCocycle.pullback_comp, hi₀, hi₁] at hc
  exact hc

end

end OAI.RepresentationTheory.Theta.Geometric
