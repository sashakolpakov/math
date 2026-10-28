import OAI.RepresentationTheory.Theta.Geometric.NonvanishingScalarPullback
import OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover

/-! # Transition Units -/

namespace OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits

noncomputable section

/-! Changes between actual rank-one frames are actual regular units. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

def frameTransitionTopUnit {X : Scheme} {M : X.Modules}
    (e g : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) : Γ(X, ⊤)ˣ :=
  ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff (g.inv ≫ e.hom)).mp inferInstance).unit

theorem frameTransitionTopUnit_value {X : Scheme} {M : X.Modules}
    (e g : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    (frameTransitionTopUnit e g : Γ(X, ⊤)) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (g.inv ≫ e.hom) :=
  ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff (g.inv ≫ e.hom)).mp inferInstance).unit_spec

theorem frameTransitionTopUnit_spec {X : Scheme} {M : X.Modules}
    (e g : M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (frameTransitionTopUnit e g : Γ(X, ⊤)) := by
  rw [frameTransitionTopUnit_value, NonvanishingScalarPullback.unitEndomorphism_endValue, Iso.hom_inv_id_assoc]

def frameTransitionUnit {X : Scheme} (M : X.Modules) (U : X.Opens)
    (e g : M.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) : Γ(X, U)ˣ :=
  Units.map U.topIso.hom.hom.toMonoidHom (frameTransitionTopUnit e g)

theorem frameTransitionUnit_spec {X : Scheme} (M : X.Modules) (U : X.Opens)
    (e g : M.restrict U.ι ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) :
    e.hom = g.hom ≫ AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection (U.topIso.inv (frameTransitionUnit M U e g : Γ(X, U))) := by
  have h : U.topIso.inv (frameTransitionUnit M U e g : Γ(X, U)) =
      (frameTransitionTopUnit e g : Γ(U.toScheme, ⊤)) := by
    change U.topIso.inv (U.topIso.hom _) = _
    exact U.topIso.hom_inv_id_apply _
  rw [h]
  exact frameTransitionTopUnit_spec e g

end

end OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits
