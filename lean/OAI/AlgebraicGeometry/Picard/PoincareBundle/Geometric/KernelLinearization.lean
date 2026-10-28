import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalKernelLinearization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Kernel Linearization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

noncomputable section

/-!
# Geometric line-bundle descent data from an actual kernel linearization
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

/-- The actual module-sheaf pullback pseudofunctor on schemes. -/
def modulePullbacks : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Bicategory.Adj.forget₁

/-- Module sheaves on schemes over a fixed base, with their actual pullback functors. -/
def overModulePullbacks (S : Scheme.{u}) :
    Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat :=
  (Over.forget S).op.toPseudofunctor.comp modulePullbacks

theorem overModulePullbacks_map {S : Scheme.{u}} {T A : Over S} (x : T ⟶ A) :
    ((overModulePullbacks S).map x.op.toLoc).toFunctor = Scheme.Modules.pullback x.left := rfl

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle A.left)

/-- A line-bundle isomorphism on the actual kernel-action scheme with its unit and cocycle. -/
abbrev LineLinearization :=
  GlobalKernelLinearization.ActionLinearization f (overModulePullbacks S) L.sheaf

/-- The ordinary geometric descent datum constructed from the line-bundle linearization. -/
def lineDescentData (D : LineLinearization f L) :
    (overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f) :=
  GlobalKernelLinearization.toDescentData f (overModulePullbacks S) L.sheaf D

/-- The object on the cover is the given geometric line bundle. -/
theorem lineDescentData_obj (D : LineLinearization f L) :
    (lineDescentData f L D).obj PUnit.unit = L.sheaf := rfl

/-- Every equal-image pair of test schemes receives the actual geometric gluing isomorphism. -/
def lineGluingIso (D : LineLinearization f L) {T : Over S} (x y : T ⟶ A)
    (h : x ≫ f = y ≫ f) :
    (Scheme.Modules.pullback x.left).obj L.sheaf ≅ (Scheme.Modules.pullback y.left).obj L.sheaf :=
  (lineDescentData f L D).iso (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y rfl h.symm

/-- The geometric gluing maps satisfy the Čech composition law over a common base map. -/
theorem lineDescentData_comp (D : LineLinearization f L) {T : Over S}
    (q : T ⟶ B) (x y z : T ⟶ A)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hz : z ≫ f = q) :
    (lineDescentData f L D).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
        (lineDescentData f L D).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) y z hy hz =
      (lineDescentData f L D).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x z hx hz :=
  (lineDescentData f L D).hom_comp q
    (i₁ := PUnit.unit) (i₂ := PUnit.unit) (i₃ := PUnit.unit) x y z hx hy hz

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
