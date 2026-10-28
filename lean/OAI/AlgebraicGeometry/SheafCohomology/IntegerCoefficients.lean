import OAI.AlgebraicGeometry.SheafCohomology.Coefficients
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-! # Integer Coefficients -/

namespace OAI.AlgebraicGeometry.SheafCohomology.IntegerCoefficients.Projective

noncomputable section

/-! Integer-module sheaves and abelian-group sheaves carry the same Ext groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

abbrev integerSheafForget (X : TopCat.{0}) :=
  sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0})

instance integerSheafForget_essSurj (X : TopCat.{0}) :
    (integerSheafForget X).EssSurj where
  mem_essImage F := by
    let e := (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).asEquivalence
    let G := (sheafCompose (Opens.grothendieckTopology X) e.inverse).obj F
    refine ⟨G, ⟨(fullyFaithfulSheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{0}).preimageIso ?_⟩⟩
    exact Functor.associator F.obj e.inverse e.functor ≪≫
      Functor.isoWhiskerLeft F.obj e.counitIso ≪≫ Functor.rightUnitor F.obj

instance integerSheafForget_isEquivalence (X : TopCat.{0}) :
    (integerSheafForget X).IsEquivalence where

instance integerSheafForget_additive (X : TopCat.{0}) :
    (integerSheafForget X).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    ext U x
    rfl

def integerSheafExtEquiv (X : TopCat.{0})
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ))]
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
    (M N : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℤ)) (n : ℕ) :
    Abelian.Ext M N n ≃+
      Abelian.Ext ((integerSheafForget X).obj M) ((integerSheafForget X).obj N) n :=
  AddEquiv.ofBijective ((integerSheafForget X).mapExtAddHom M N n)
    ((integerSheafForget X).mapExt_bijective_of_preservesInjectiveObjects M N n)

end

end OAI.AlgebraicGeometry.SheafCohomology.IntegerCoefficients.Projective
