import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticPullbackTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChernComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction

/-! # Chern Embedding Independence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernEmbeddingIndependence

noncomputable section

section

/-! The native rational Chern class of an actual algebraic line bundle
commutes with every complex scheme map between the given smooth
projective presentations. Local frames and logarithms are pulled back
constructively, and comparison with the original chosen frames is proved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback

theorem lineBundleChernClass_pullback {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : Y.toOver ⟶ X.toOver) (L : HilbertConstruction.Line.Bundles.LineBundle X.carrier) :
    Intrinsic.ChernClasses.lineBundleChernClass Y (L.pullback f.left) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 2 (Intrinsic.ChernClasses.lineBundleChernClass X L) := by
  let B := Intrinsic.ChernClasses.nativeLineBundle X L
  let g := TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)
  let U := HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover g B.logCover
  have hU := HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover_covers g B.logCover B.logCover_covers
  let l := HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.logarithmPullback g B.logCover B.bundleLogCech
  have hl := HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.exponentialCocycle_pullback g B.logCover B.bundleLogCech B.bundleLogCech_cocycle
  let r (i : B.LogCoverIndex) := Local.PullbackFrames.pullbackLocalFrame f.left L.sheaf (Frame.ChernComparison.chosenLineFrame B (B.logParent i))
  have hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen Y (r i) := by
    intro i p hp
    exact B.logCover_subset i hp
  have he : ∀ (a : Fin 2 → B.LogCoverIndex) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp (l a p) = AnalyticFrameTransitions.framePointTransition Y (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)) := by
    intro a p
    have h := B.bundleLogCech_exp_point a (HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.intersectionMap g B.logCover a p)
    have hchosen := Frame.ChernComparison.chosenLineFrame_transition B (B.logParent (a 0)) (B.logParent (a 1))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p.val)
      (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
      (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))
    have hpull := AnalyticPullbackTransitions.pullbackFrame_pointTransition f
      (Frame.ChernComparison.chosenLineFrame B (B.logParent (a 0))) (Frame.ChernComparison.chosenLineFrame B (B.logParent (a 1)))
      p.val (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
      (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))
    exact h.trans (hchosen.symm.trans hpull.symm)
  exact (Frame.ChernComparison.firstChernClass_eq_frameLogs (Intrinsic.ChernClasses.nativeLineBundle Y (L.pullback f.left))
    U hU r hr l hl he).trans
      (HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.logarithmicSingularClass_pullback g B.logCover B.logCover_covers
        B.bundleLogCech B.bundleLogCech_cocycle)

end

/-! The actual native Chern class is independent of a chosen projective
embedding of the same complex scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem lineBundleChernClass_changeEmbedding (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (Q : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.carrier X.structureMap) (L : HilbertConstruction.Line.Bundles.LineBundle X.carrier) :
    Intrinsic.ChernClasses.lineBundleChernClass {X with projective := Q} L = Intrinsic.ChernClasses.lineBundleChernClass X L := by
  let Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation := {X with projective := Q}
  have hi := Intrinsic.ChernClasses.lineBundleChernClass_iso Y (L.pullback (𝟙 X.carrier)) L
    ((Scheme.Modules.pullbackId X.carrier).app L.sheaf)
  have hp := lineBundleChernClass_pullback (X := X) (Y := Y) (𝟙 X.toOver) L
  have hmap : TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (𝟙 X.toOver)) =
      𝟙 (Betti.Scheme.schemePointSpace X.toOver) := by
    ext p
    exact congrArg (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver => q.left) (Category.comp_id p)
  have hc := congrArg (fun f => AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 2
    (Intrinsic.ChernClasses.lineBundleChernClass X L)) hmap
  have hid := congrArg (fun f => f (Intrinsic.ChernClasses.lineBundleChernClass X L))
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace X.toOver) 2)
  exact hi.symm.trans (hp.trans (hc.trans hid))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernEmbeddingIndependence
