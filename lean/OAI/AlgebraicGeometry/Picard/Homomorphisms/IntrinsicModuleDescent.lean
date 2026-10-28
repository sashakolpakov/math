import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

/-! # Intrinsic Module Descent -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.IntrinsicModuleDescent

noncomputable section

/-! Ordinary module descent data written directly in the native scheme
module categories. This exposes the existing pseudofunctor datum without
changing its object, gluing maps, or equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

structure NativeModuleDescent where
  module : X.Modules
  hom {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Scheme.Modules.pullback x).obj module ⟶ (Scheme.Modules.pullback y).obj module
  hom_self {T : Scheme.{u}} (q : T ⟶ Y) (x : T ⟶ X) (hx : x ≫ f = q) :
    hom q x x hx hx = 𝟙 _
  hom_comp {T : Scheme.{u}} (q : T ⟶ Y) (x y z : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hz : z ≫ f = q) :
    hom q x y hx hy ≫ hom q y z hy hz = hom q x z hx hz
  hom_pullback {T T' : Scheme.{u}} (t : T' ⟶ T) (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Scheme.Modules.pullbackComp t x).inv.app module ≫
      (Scheme.Modules.pullback t).map (hom q x y hx hy) ≫
        (Scheme.Modules.pullbackComp t y).hom.app module =
      hom (t ≫ q) (t ≫ x) (t ≫ y)
        (by rw [Category.assoc, hx]) (by rw [Category.assoc, hy])

def NativeModuleDescent.ofPseudofunctor
    (D : PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)) : NativeModuleDescent f where
  module := D.obj PUnit.unit
  hom q x y hx hy := D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy
  hom_self q x hx := D.hom_self q (i := PUnit.unit) x hx
  hom_comp q x y z hx hy hz :=
    D.hom_comp q (i₁ := PUnit.unit) (i₂ := PUnit.unit) (i₃ := PUnit.unit) x y z hx hy hz
  hom_pullback t q x y hx hy := by
    have h := PoincareBundle.Geometric.DescentEquations.hom_pullback D t q (t ≫ q) rfl
      (i := PUnit.unit) (j := PUnit.unit) x y hx hy (t ≫ x) (t ≫ y) rfl rfl
    exact h

variable {f} (D : NativeModuleDescent f)

def NativeModuleDescent.iso {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Scheme.Modules.pullback x).obj D.module ≅ (Scheme.Modules.pullback y).obj D.module where
  hom := D.hom q x y hx hy
  inv := D.hom q y x hy hx
  hom_inv_id := (D.hom_comp q x y x hx hy hx).trans (D.hom_self q x hx)
  inv_hom_id := (D.hom_comp q y x y hy hx hy).trans (D.hom_self q y hy)

instance NativeModuleDescent.hom_isIso {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) : IsIso (D.hom q x y hx hy) :=
  (D.iso q x y hx hy).isIso_hom

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.IntrinsicModuleDescent
