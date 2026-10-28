import OAI.RepresentationTheory.Theta.Geometric.SchemeLineCocycle
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF

/-! # Continuous Line -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Continuous transition cocycles, their actual continuous pullbacks,
and the cocycle constructed from an arbitrary complex scheme line bundle. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback

structure ContinuousLine.ContinuousLineCocycle (T : TopCat) (I : Type) where
  cover : I → Opens T
  covers : ∀ x, ∃ i, x ∈ cover i
  transition : AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.LogCechCochain T cover
  nonzero : ∀ a p, transition a p ≠ 0
  cocycle : ∀ (a : Fin 3 → I) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection cover a),
    transition (a ∘ (2 : Fin 3).succAbove)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp cover a _ p.property⟩ *
      transition (a ∘ (0 : Fin 3).succAbove)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp cover a _ p.property⟩ =
    transition (a ∘ (1 : Fin 3).succAbove)
      ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp cover a _ p.property⟩

namespace ContinuousLine.ContinuousLineCocycle

variable {T Y : TopCat} {I : Type} (C : ContinuousLineCocycle T I)

def pullback (f : Y ⟶ T) : ContinuousLineCocycle Y I where
  cover := AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover f C.cover
  covers := AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover_covers f C.cover C.covers
  transition a := (C.transition a).comp (AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.intersectionMap f C.cover a).hom
  nonzero a p := C.nonzero a (AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.intersectionMap f C.cover a p)
  cocycle a p := C.cocycle a (AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.intersectionMap f C.cover a p)

theorem pullback_transition (f : Y ⟶ T) (a : Fin 2 → I)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (C.pullback f).cover a) :
    (C.pullback f).transition a p = C.transition a (AlgebraicGeometry.HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.intersectionMap f C.cover a p) := rfl

end ContinuousLine.ContinuousLineCocycle

def SchemeLineFrame.SchemeLineAtlas.continuousCocycle {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left}
    (A : SchemeLineFrame.SchemeLineAtlas L) : ContinuousLine.ContinuousLineCocycle (TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) X.left where
  cover := A.analyticCover
  covers := A.analyticCover_covers
  transition := A.transitionCech
  nonzero := A.transitionCech_ne_zero
  cocycle := A.transitionCech_cocycle

end

end OAI.RepresentationTheory.Theta.Geometric
