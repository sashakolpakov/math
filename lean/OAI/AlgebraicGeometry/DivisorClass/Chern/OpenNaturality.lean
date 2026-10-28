import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.AnalyticGauge
import OAI.AlgebraicGeometry.DivisorClass.Chern.Iso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction

/-! # Open Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OpenNaturality

noncomputable section

/-!
# ChernClass: the actual first Chern class commutes with open restriction

The original logarithms pull back along the genuine analytic map. On a
common refinement, the actual mixed section frames give a continuous gauge
between these logarithms and those of the restricted algebraic line bundle.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Restricting the actual sheaf to an open complex subscheme pulls back its
original logarithmic first Chern class. The chosen frames need not agree. -/
theorem firstChernClassQ_restrictToOpen {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (L : Line.Bundles.AlgebraicLineBundle X) (f : Y.toOver ⟶ X.toOver) [IsOpenImmersion f.left] :
    First.firstChernClassQ Y (L.restrictToOpen Y f.left) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 2 (First.firstChernClassQ X L) := by
  let M := L.restrictToOpen Y f.left
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver)
  let g := TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)
  let U := HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover g L.logCover
  have hU := HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover_covers g L.logCover L.logCover_covers
  let l := HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.logarithmPullback g L.logCover L.bundleLogCech
  have hl := HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.exponentialCocycle_pullback g L.logCover L.bundleLogCech L.bundleLogCech_cocycle
  let W : L.LogCoverIndex × M.LogCoverIndex → Opens T := fun a => U a.1 ⊓ M.logCover a.2
  have hW : ∀ y, ∃ a, y ∈ W a := by
    intro y
    obtain ⟨i, hi⟩ := hU y
    obtain ⟨j, hj⟩ := M.logCover_covers y
    exact ⟨(i, j), hi, hj⟩
  have hWU : ∀ a, W a ≤ U a.1 := fun _ => inf_le_left
  have hWM : ∀ a, W a ≤ M.logCover a.2 := fun _ => inf_le_right
  let k := LogRefinement.RationalCech.refineLogCech T U W Prod.fst hWU l
  let k' := LogRefinement.RationalCech.refineLogCech T M.logCover W Prod.snd hWM M.bundleLogCech
  have hk := LogRefinement.RationalCech.exponentialCocycle_refinement T U W Prod.fst hWU l hl
  have hk' := LogRefinement.RationalCech.exponentialCocycle_refinement T M.logCover W Prod.snd hWM
    M.bundleLogCech M.bundleLogCech_cocycle
  let u (a : L.LogCoverIndex × M.LogCoverIndex) : C(W a, ℂ) :=
    (L.openMixedTransitionPair f (L.logParent a.1) (M.logParent a.2)).comp
      ⟨fun y => ⟨y.val, L.logCover_subset a.1 y.property.1,
        M.logCover_subset a.2 y.property.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hu : ∀ a y, u a y ≠ 0 := fun a y =>
    L.openMixedTransitionPair_ne_zero f (L.logParent a.1) (M.logParent a.2) _
  have hc : LogCech.RationalCech.logarithmicSingularClass T W hW k' hk' = LogCech.RationalCech.logarithmicSingularClass T W hW k hk := by
    apply ContinuousGauge.RationalCech.logarithmicSingularClass_continuous_gauge T W u hu hW k k' hk hk'
    intro a p
    have hleft := M.bundleLogCech_exp_point (Prod.snd ∘ a)
      ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le M.logCover W Prod.snd hWM a p.property⟩
    have hright := L.bundleLogCech_exp_point (Prod.fst ∘ a)
      (HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.intersectionMap g L.logCover (Prod.fst ∘ a)
        ⟨p.val, Rational.Cech.RationalCech.cechIntersection_refinement_le U W Prod.fst hWU a p.property⟩)
    change Complex.exp (k' a p) = _ at hleft
    change Complex.exp (k a p) = _ at hright
    rw [hleft, hright]
    exact L.openMixedPointTransition_gauge f
      (L.logParent (a 0).1) (L.logParent (a 1).1)
      (M.logParent (a 0).2) (M.logParent (a 1).2) p.val
      (L.logCover_subset (a 0).1 (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le W a 0 p.property).1)
      (L.logCover_subset (a 1).1 (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le W a 1 p.property).1)
      (M.logCover_subset (a 0).2 (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le W a 0 p.property).2)
      (M.logCover_subset (a 1).2 (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le W a 1 p.property).2)
  exact (LogRefinement.RationalCech.logarithmicSingularClass_refinement T M.logCover W Prod.snd hWM
    M.logCover_covers hW M.bundleLogCech M.bundleLogCech_cocycle).symm.trans
    (hc.trans ((LogRefinement.RationalCech.logarithmicSingularClass_refinement T U W Prod.fst hWU hU hW l hl).trans
      (HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.logarithmicSingularClass_pullback g L.logCover L.logCover_covers
        L.bundleLogCech L.bundleLogCech_cocycle)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OpenNaturality
