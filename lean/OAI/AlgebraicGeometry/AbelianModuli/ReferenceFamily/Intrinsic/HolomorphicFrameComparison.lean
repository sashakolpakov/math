import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.FrameClass

/-! # Holomorphic Frame Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFrameComparison

noncomputable section

/-! A closed cocycle of actual algebraic frame units computes the
original native holomorphic class of the line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

theorem nativeHolomorphicLineClass_eq_frameCech (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier) {I : Type}
    (U : I → Opens V.analyticSpace) (hU : ∀ x, ∃ i, x ∈ U i)
    (r : I → LineFrameAtlas.LocalLineFrame L.sheaf)
    (hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation (r i))
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1 k = 0)
    (he : ∀ (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      (Holomorphic.LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (k a)).val x =
        AnalyticFrameTransitions.framePointTransition V.presentation (r (a 0)) (r (a 1)) x.val
          (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
          (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property))) :
    HolomorphicLineClass.nativeHolomorphicLineClass V L =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of V.analyticSpace) U
        (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace)
        (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of V.analyticSpace) U hU) 0 k hk := by
  let B := ChernClasses.nativeLineBundle V.presentation L
  let k' := Holomorphic.LogUnitClass.holomorphicLogUnitCech V.analyticModel V.analyticSpace B.logCover B.bundleLogCech
    (HolomorphicLineClass.nativeBundleLogCech_holomorphic V L)
  have hk' := Holomorphic.LogUnitClass.holomorphicLogUnitCech_closed V.analyticModel V.analyticSpace B.logCover B.bundleLogCech
    (HolomorphicLineClass.nativeBundleLogCech_holomorphic V L) B.bundleLogCech_cocycle
  apply Holomorphic.FrameClass.frameUnitCech_class_cover_independent V U hU B.logCover B.logCover_covers r
    (fun i => Frame.ChernComparison.chosenLineFrame B (B.logParent i)) hr B.logCover_subset k k' hk hk' he
  intro a x
  exact (HolomorphicLineClass.nativeHolomorphicLineClass_transition V L a x).trans
    (Frame.ChernComparison.chosenLineFrame_transition B (B.logParent (a 0)) (B.logParent (a 1)) x.val
      (B.logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le B.logCover a 0 x.property))
      (B.logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le B.logCover a 1 x.property))).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFrameComparison
