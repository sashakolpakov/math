import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicFrameComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.OneCocycleValues

/-! # Frame Unit Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameUnitCocycle

noncomputable section

/-! Original regular algebraic frame units directly define a closed
holomorphic cocycle and compute the native line-bundle class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {B : V.carrier.Modules} {I : Type}
  (U : I → Opens V.analyticSpace) (r : I → LineFrameAtlas.LocalLineFrame B)
  (hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation (r i))

def frameUnitCech : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1 :=
  fun a => Additive.ofMul (Units.map
    (DivisorClass.Chern.HolomorphicSection.Data.holomorphicOpenRestriction (E := V.analyticModel)
      (le_inf ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0).trans (hr (a 0)))
        ((AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1).trans (hr (a 1))))).toMonoidHom
    (Holomorphic.FrameClass.frameHolomorphicUnit V (r (a 0)) (r (a 1))))

theorem frameUnitCech_value (a : Fin 2 → I) (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) :
    (Holomorphic.LogUnitClass.holomorphicUnitSection V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
      (frameUnitCech V U r hr a)).val x =
      AnalyticFrameTransitions.framePointTransition V.presentation (r (a 0)) (r (a 1)) x.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property)) := rfl

theorem frameUnitCech_closed :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj U 1
      (frameUnitCech V U r hr) = 0 := by
  apply Cech.OneCocycleValues.abelianCech_one_closed_of_transition (X := TopCat.of V.analyticSpace) U
    (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace).obj
  intro a
  apply Holomorphic.GlobalGluing.holomorphicUnitSection_ext V.analyticModel V.analyticSpace (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
  intro x
  have h0 := hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 x.property)
  have h1 := hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 x.property)
  have h2 := hr (a 2) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 2 x.property)
  change AnalyticFrameTransitions.framePointTransition V.presentation (r (a 1)) (r (a 2)) x.val h1 h2 *
    AnalyticFrameTransitions.framePointTransition V.presentation (r (a 0)) (r (a 1)) x.val h0 h1 =
      AnalyticFrameTransitions.framePointTransition V.presentation (r (a 0)) (r (a 2)) x.val h0 h2
  exact (mul_comm _ _).trans (AnalyticFrameTransitions.framePointTransition_cocycle V.presentation
    (r (a 0)) (r (a 1)) (r (a 2)) x.val h0 h1 h2)

theorem nativeHolomorphicLineClass_frameUnits (L : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
    (s : I → LineFrameAtlas.LocalLineFrame L.sheaf) (hs : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen V.presentation (s i))
    (hU : ∀ x, ∃ i, x ∈ U i) :
    HolomorphicLineClass.nativeHolomorphicLineClass V L = DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of V.analyticSpace) U
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicUnitsSheaf V.analyticModel V.analyticSpace)
      (DivisorClass.Chern.Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of V.analyticSpace) U hU) 0
      (frameUnitCech V U s hs) (frameUnitCech_closed V U s hs) :=
  HolomorphicFrameComparison.nativeHolomorphicLineClass_eq_frameCech V L U hU s hs (frameUnitCech V U s hs)
    (frameUnitCech_closed V U s hs) (frameUnitCech_value V U s hs)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameUnitCocycle
