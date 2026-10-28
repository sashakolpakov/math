import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.SheafInverseImage
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Topology.Sheaves.Abelian

/-! # Cohomology Inverse Image -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyInverseImage

noncomputable section

/-! A continuous map induces an additive map on actual sheaf cohomology by exact inverse image. The source constant sheaf is transported by the proved adjunction comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

def additiveSheafCohomologyInverseImage
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n :
      _ ⥤ AddCommGrpCat.{u}).obj F) →+
      ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n :
        _ ⥤ AddCommGrpCat.{u}).obj ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F)) := by
  let L : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} f
  have : L.Additive := Constant.SheafInverseImage.additiveSheafInverseImage_additive f
  have : PreservesFiniteLimits L := Constant.SheafInverseImage.additiveSheafInverseImage_preservesFiniteLimits f
  have : PreservesFiniteColimits L :=
    inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f))
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let e : L.obj ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj Z) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj Z :=
    (Constant.SheafInverseImage.constantSheafInverseImageIso f).app Z
  exact ((Ext.mk₀ e.inv).precomp (L.obj F) (zero_add n)).comp
    (L.mapExtAddHom
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj Z) F n)

theorem additiveSheafCohomologyInverseImage_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}} (a : F ⟶ G) (n : ℕ)
    (x : (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n :
      _ ⥤ AddCommGrpCat.{u}).obj F) :
    additiveSheafCohomologyInverseImage f G n (CategoryTheory.Sheaf.H.map a n x) =
      CategoryTheory.Sheaf.H.map ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map a) n
        (additiveSheafCohomologyInverseImage f F n x) := by
  let L : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} f
  have : L.Additive := Constant.SheafInverseImage.additiveSheafInverseImage_additive f
  have : PreservesFiniteLimits L := Constant.SheafInverseImage.additiveSheafInverseImage_preservesFiniteLimits f
  have : PreservesFiniteColimits L :=
    inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f))
  let ZY := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let ZX := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let e : L.obj ZY ≅ ZX := (Constant.SheafInverseImage.constantSheafInverseImageIso f).app
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let x' : Ext.{u} ZY F n := x
  have hm : (x'.comp (Ext.mk₀ a) (add_zero n)).mapExactFunctor L =
      (x'.mapExactFunctor L).comp (Ext.mk₀ (L.map a)) (add_zero n) :=
    (Ext.mapExactFunctor_comp L x' (Ext.mk₀ a) (add_zero n)).trans
      (congrArg (fun z : Ext.{u} (L.obj F) (L.obj G) 0 =>
        (x'.mapExactFunctor L).comp z (add_zero n))
          (Ext.mapExactFunctor_mk₀ L a))
  change (Ext.mk₀ e.inv).comp
      ((x'.comp (Ext.mk₀ a) (add_zero n)).mapExactFunctor L) (zero_add n) =
    ((Ext.mk₀ e.inv).comp (x'.mapExactFunctor L) (zero_add n)).comp
      (Ext.mk₀ (L.map a)) (add_zero n)
  exact (congrArg (fun z : Ext.{u} (L.obj ZY) (L.obj G) n =>
    (Ext.mk₀ e.inv).comp z (zero_add n)) hm).trans
      (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ e.inv)
        (x'.mapExactFunctor L) (Ext.mk₀ (L.map a)) (zero_add n)).symm

def additiveSheafCohomologyPullbackMap
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}}
    {G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F ⟶ G) (n : ℕ) :
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology Y) n :
      _ ⥤ AddCommGrpCat.{u}).obj F) →+
      ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n :
        _ ⥤ AddCommGrpCat.{u}).obj G) := by
  let L : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    TopCat.Sheaf.pullback AddCommGrpCat.{u} f
  have : L.Additive := Constant.SheafInverseImage.additiveSheafInverseImage_additive f
  have : PreservesFiniteLimits L := Constant.SheafInverseImage.additiveSheafInverseImage_preservesFiniteLimits f
  have : PreservesFiniteColimits L :=
    inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f))
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let ZY := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj Z
  let ZX := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj Z
  let e : L.obj ZY ≅ ZX := (Constant.SheafInverseImage.constantSheafInverseImageIso f).app Z
  let a' : L.obj F ⟶ G := a
  let v : Ext.{u} ZX (L.obj F) n →+ Ext.{u} ZX G n :=
    (Ext.mk₀ a').postcomp ZX (add_zero n)
  let u : Ext.{u} ZY F n →+ Ext.{u} ZX (L.obj F) n :=
    ((Ext.mk₀ e.inv).precomp (L.obj F) (zero_add n)).comp (L.mapExtAddHom ZY F n)
  exact v.comp u

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyInverseImage
