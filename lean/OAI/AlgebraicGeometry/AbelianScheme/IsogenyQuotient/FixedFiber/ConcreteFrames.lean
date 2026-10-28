import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.FramePullbackUnit
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.LineFrameCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.LineFramePullback

/-! # Concrete Frames -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.ConcreteFrames.Construction

noncomputable section

/-! The units in the original fixed-fiber logarithmic cocycle are
the transitions of the actual pulled line frames, including along
nonflat base changes. The frame compatibility is derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (R k : Type) [CommRing R] [CommRing k] [Algebra R k]
    (X : Over (Spec (.of R))) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)
    (C : AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover L) (V : X.left.affineOpens)
    (i j : C.cover.I₀) (hi : V.1 ≤ (C.cover.f i).opensRange)
    (hj : V.1 ≤ (C.cover.f j).opensRange)

theorem fixedFiberReducedUnit_actualFrameTransition :
    Units.map (AbelianModuli.ReferenceFamily.FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R k X V).toMonoidHom
      (AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle.fixedFiberFrameReducedUnit R k X (fun a => (C.cover.f a).opensRange)
        C.transitions V i j hi hj) =
      ((C.localFrame i).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R k X)).transition
        ((C.localFrame j).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R k X))
        (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen R k X V)
        ((AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R k X).preimage_mono hi)
        ((AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R k X).preimage_mono hj) := by
  rw [AbelianModuli.ReferenceFamily.FixedFiber.FramePullbackUnit.fixedFiberFrameReducedUnit_original, AbelianModuli.ReferenceFamily.Constructed.LineFrameCover.LineBundleAffineFrameCover.transition_eq_original]
  exact (AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame.pullbackBy_transition (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R k X)
    (C.localFrame i) (C.localFrame j) V.val hi hj).symm

theorem fixedFiberActualFrameTransition_coordinates :
    Units.map (AbelianModuli.ReferenceFamily.FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R k X V).symm.toMonoidHom
      (((C.localFrame i).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R k X)).transition
        ((C.localFrame j).pullbackBy (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R k X))
        (AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFiberAffineOpen R k X V)
        ((AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R k X).preimage_mono hi)
        ((AbelianModuli.ReferenceFamily.FixedFiber.CoordinateProjection.fixedFamilyProjection R k X).preimage_mono hj)) =
      AbelianModuli.ReferenceFamily.FixedFiber.LineLogCocycle.fixedFiberFrameReducedUnit R k X (fun a => (C.cover.f a).opensRange)
        C.transitions V i j hi hj := by
  rw [← fixedFiberReducedUnit_actualFrameTransition R k X L C V i j hi hj]
  apply Units.ext
  exact (AbelianModuli.ReferenceFamily.FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R k X V).symm_apply_apply _

theorem localLineFrame_transition_transport {Y : Scheme.{0}} {M : Y.Modules}
    (s t : AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) {U W : Y.Opens} (h : U = W)
    (hs : U ≤ s.domain) (ht : U ≤ t.domain) (hs' : W ≤ s.domain) (ht' : W ≤ t.domain) :
    Units.map (AbelianModuli.ReferenceFamily.Regular.SectionTransport.regularSectionTransport h).toMonoidHom (s.transition t U hs ht) =
      s.transition t W hs' ht' := by
  subst W
  apply Units.ext
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FixedFiber.ConcreteFrames.Construction
