import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackCoherence
import OAI.AlgebraicGeometry.Picard.Homomorphisms.IntrinsicModuleDescent

/-! # Framed Descent Scalars -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentScalars

noncomputable section

/-! Scalar-valued descent maps for a module sheaf with a chosen global
frame. The scalar is the actual endomorphism of the structure module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} {L : X.Modules}

def pulledModuleFrame (e : L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) {T : Scheme.{u}} (x : T ⟶ X) :
    (Scheme.Modules.pullback x).obj L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T :=
  (Scheme.Modules.pullback x).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x

@[reassoc]
theorem pulledModuleFrame_comp (e : L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    {T T' : Scheme.{u}} (x : T ⟶ X) (t : T' ⟶ T) :
    (Scheme.Modules.pullbackComp t x).hom.app L ≫ (pulledModuleFrame e (t ≫ x)).hom =
      (Scheme.Modules.pullback t).map (pulledModuleFrame e x).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom := by
  simp only [pulledModuleFrame, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  rw [← Category.assoc, ← NatTrans.naturality, Category.assoc,
    UnitPullbackCoherence.Construction.structureModulePullback_comp]
  rfl

variable {Y : Scheme.{u}} {f : X ⟶ Y}
variable (D : IntrinsicModuleDescent.Construction.NativeModuleDescent f)
variable (e : D.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

def framedDescentEnd {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) :=
  (pulledModuleFrame e x).inv ≫
    D.hom q x y hx hy ≫
      (pulledModuleFrame e y).hom

instance framedDescentEnd_isIso {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) : IsIso (framedDescentEnd D e q x y hx hy) := by
  dsimp [framedDescentEnd]
  infer_instance

@[simp]
theorem framedDescentEnd_self {T : Scheme.{u}} (q : T ⟶ Y) (x : T ⟶ X)
    (hx : x ≫ f = q) : framedDescentEnd D e q x x hx hx = 𝟙 _ := by
  simp only [framedDescentEnd, D.hom_self, Category.id_comp, Iso.inv_hom_id]

theorem framedDescentEnd_comp {T : Scheme.{u}} (q : T ⟶ Y) (x y z : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hz : z ≫ f = q) :
    framedDescentEnd D e q x y hx hy ≫ framedDescentEnd D e q y z hy hz =
      framedDescentEnd D e q x z hx hz := by
  simp only [framedDescentEnd, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (D.hom q x y hx hy), D.hom_comp]

def framedDescentScalar {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) : Γ(T, ⊤) :=
  AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T (framedDescentEnd D e q x y hx hy)

theorem framedDescentScalar_congr {T : Scheme.{u}}
    (q q' : T ⟶ Y) (x x' y y' : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hx' : x' ≫ f = q') (hy' : y' ≫ f = q')
    (hq : q = q') (hxx : x = x') (hyy : y = y') :
    framedDescentScalar D e q x y hx hy = framedDescentScalar D e q' x' y' hx' hy' := by
  cases hq
  cases hxx
  cases hyy
  rfl

theorem framedDescentScalar_isUnit {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) : IsUnit (framedDescentScalar D e q x y hx hy) :=
  (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEnd_isIso_iff _).mp inferInstance

@[simp]
theorem framedDescentScalar_self {T : Scheme.{u}} (q : T ⟶ Y) (x : T ⟶ X)
    (hx : x ≫ f = q) : framedDescentScalar D e q x x hx hx = 1 := by
  rw [framedDescentScalar, framedDescentEnd_self]
  exact map_one (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T)

theorem framedDescentScalar_comp {T : Scheme.{u}} (q : T ⟶ Y) (x y z : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hz : z ≫ f = q) :
    framedDescentScalar D e q x y hx hy * framedDescentScalar D e q y z hy hz =
      framedDescentScalar D e q x z hx hz := by
  rw [mul_comm]
  exact (map_mul (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T) _ _).symm.trans
    (congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T) (framedDescentEnd_comp D e q x y z hx hy hz))

theorem framedDescentEnd_pullback {T T' : Scheme.{u}} (t : T' ⟶ T)
    (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    UnitPullbackScalars.Construction.unitEndPullback t (framedDescentEnd D e q x y hx hy) =
      framedDescentEnd D e (t ≫ q) (t ≫ x) (t ≫ y)
        (by rw [Category.assoc, hx]) (by rw [Category.assoc, hy]) := by
  have hd := D.hom_pullback t q x y hx hy
  dsimp [UnitPullbackScalars.Construction.unitEndPullback, framedDescentEnd]
  rw [Functor.map_comp, Functor.map_comp, ← hd]
  have hy' := pulledModuleFrame_comp e y t
  rw [← cancel_epi ((Scheme.Modules.pullback t).map (pulledModuleFrame e x).hom ≫
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.map_hom_inv_id_assoc]
  rw [← pulledModuleFrame_comp_assoc e x t]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id_app_assoc]
  rw [hy']

theorem framedDescentScalar_pullback {T T' : Scheme.{u}} (t : T' ⟶ T)
    (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    t.appTop (framedDescentScalar D e q x y hx hy) =
      framedDescentScalar D e (t ≫ q) (t ≫ x) (t ≫ y)
        (by rw [Category.assoc, hx]) (by rw [Category.assoc, hy]) :=
  (UnitPullbackScalars.Construction.unitEndPullback_scalar t _).symm.trans
    (congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T') (framedDescentEnd_pullback D e t q x y hx hy))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentScalars
