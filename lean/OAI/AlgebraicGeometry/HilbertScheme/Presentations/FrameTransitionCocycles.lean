import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Frame Transition Cocycles -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameTransitionCocycles

noncomputable section

/-! Frame transitions are invertible regular functions and satisfy
the cocycle identity as actual structure-sheaf sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

universe u
variable {X : Scheme.{u}} {M N : X.Modules}

def frameTransitionValue (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) : Γ(X, ⊤) :=
  AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (e.inv ≫ f.hom)

theorem frameTransitionValue_isUnit (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    IsUnit (frameTransitionValue e f) :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff (e.inv ≫ f.hom)).mp inferInstance

theorem frameTransitionValue_self (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) : frameTransitionValue e e = 1 := by
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (e.inv ≫ e.hom) = 1
  rw [Iso.inv_hom_id]
  exact map_one (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X)

theorem frameTransitionValue_cocycle (e f g : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    frameTransitionValue e f * frameTransitionValue f g = frameTransitionValue e g := by
  unfold frameTransitionValue
  rw [mul_comm, ← map_mul]
  change AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X ((e.inv ≫ f.hom) ≫ (f.inv ≫ g.hom)) =
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X (e.inv ≫ g.hom)
  rw [Category.assoc, Iso.hom_inv_id_assoc]

theorem frameTransitionValue_change_source (h : N ≅ M) (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    frameTransitionValue (h ≪≫ e) (h ≪≫ f) = frameTransitionValue e f := by
  unfold frameTransitionValue
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]

def frameTransitionUnit (e f : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) : Γ(X, ⊤)ˣ :=
  (frameTransitionValue_isUnit e f).unit

theorem frameTransitionUnit_cocycle (e f g : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    frameTransitionUnit e f * frameTransitionUnit f g = frameTransitionUnit e g := by
  apply Units.ext
  change (frameTransitionValue_isUnit e f).unit.val * (frameTransitionValue_isUnit f g).unit.val =
    (frameTransitionValue_isUnit e g).unit.val
  rw [(frameTransitionValue_isUnit e f).unit_spec, (frameTransitionValue_isUnit f g).unit_spec,
    (frameTransitionValue_isUnit e g).unit_spec, frameTransitionValue_cocycle]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameTransitionCocycles
