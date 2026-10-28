import OAI.RepresentationTheory.Theta.Geometric.ModuleIsoFrameUnits
import OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameComposition

/-! # Iso Unit Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoUnitPullback

noncomputable section

/-! Regular-unit coefficients of native module isomorphisms commute
with arbitrary scheme pullback, including nonflat reductions. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem frameTransitionTopUnit_unique {X : Scheme} {M : X.Modules}
    (e g : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (u : Γ(X, ⊤)ˣ)
    (h : e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (u : Γ(X, ⊤))) :
    u = IntrinsicFrame.TransitionUnits.frameTransitionTopUnit e g := by
  apply Units.ext
  have H := (cancel_epi g.hom).mp (h.symm.trans (IntrinsicFrame.TransitionUnits.frameTransitionTopUnit_spec e g))
  exact (NonvanishingScalarPullback.endValue_unitEndomorphism _).symm.trans
    ((congrArg (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X) H).trans (NonvanishingScalarPullback.endValue_unitEndomorphism _))

theorem frameTransitionTopUnit_pullback {X Y : Scheme} (f : X ⟶ Y) {M : Y.Modules}
    (e g : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    IntrinsicFrame.TransitionUnits.frameTransitionTopUnit (Pullback.FrameComposition.pullbackGlobalFrame f e) (Pullback.FrameComposition.pullbackGlobalFrame f g) =
      Units.map f.appTop.hom.toMonoidHom (IntrinsicFrame.TransitionUnits.frameTransitionTopUnit e g) := by
  symm
  apply frameTransitionTopUnit_unique
  have h := IntrinsicFrame.TransitionUnits.frameTransitionTopUnit_spec e g
  simp only [Pullback.FrameComposition.pullbackGlobalFrame, Iso.trans_hom, Functor.mapIso_hom, h,
    Functor.map_comp, Category.assoc]
  rw [Pullback.Algebraic.pullback_unitEndomorphism]
  rfl

def moduleIsoTopUnit {X : Scheme} {M N : X.Modules} (a : M ≅ N)
    (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (g : N ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) : Γ(X, ⊤)ˣ :=
  IntrinsicFrame.TransitionUnits.frameTransitionTopUnit (a ≪≫ g) e

theorem moduleIsoTopUnit_spec {X : Scheme} {M N : X.Modules} (a : M ≅ N)
    (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (g : N ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    a.hom ≫ g.hom = e.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (moduleIsoTopUnit a e g : Γ(X, ⊤)) :=
  IntrinsicFrame.TransitionUnits.frameTransitionTopUnit_spec (a ≪≫ g) e

theorem moduleIsoTopUnit_eq_one_iff {X : Scheme} {M N : X.Modules} (a : M ≅ N)
    (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (g : N ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    moduleIsoTopUnit a e g = 1 ↔ a.hom ≫ g.hom = e.hom := by
  have h1 : AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (1 : Γ(X, ⊤)) = 𝟙 (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) := by
    apply AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective X
    rw [NonvanishingScalarPullback.endValue_unitEndomorphism]
    exact (map_one (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X)).symm
  constructor
  · intro h
    simpa only [h, Units.val_one, h1, Category.comp_id] using moduleIsoTopUnit_spec a e g
  · intro h
    symm
    apply frameTransitionTopUnit_unique
    simpa only [Iso.trans_hom, Units.val_one, h1, Category.comp_id] using h

theorem moduleIsoTopUnit_pullback {X Y : Scheme} (f : X ⟶ Y) {M N : Y.Modules} (a : M ≅ N)
    (e : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (g : N ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    moduleIsoTopUnit ((Scheme.Modules.pullback f).mapIso a)
      (Pullback.FrameComposition.pullbackGlobalFrame f e) (Pullback.FrameComposition.pullbackGlobalFrame f g) =
      Units.map f.appTop.hom.toMonoidHom (moduleIsoTopUnit a e g) := by
  have h : (Scheme.Modules.pullback f).mapIso a ≪≫ Pullback.FrameComposition.pullbackGlobalFrame f g =
      Pullback.FrameComposition.pullbackGlobalFrame f (a ≪≫ g) := by
    apply Iso.ext
    simp only [Pullback.FrameComposition.pullbackGlobalFrame, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  unfold moduleIsoTopUnit
  rw [h, frameTransitionTopUnit_pullback]

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoUnitPullback
