import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientCo
import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSheafUniverses

/-! # Integer Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerSheaf.IntegerSheafEquivalence

noncomputable section

/-! Integer-module sheaves and additive sheaves have the same actual Ext groups at the native pro-étale universes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)

abbrev forgetSheaf : Sheaf J (ModuleCat.{1} ℤ) ⥤ Sheaf J AddCommGrpCat.{1} :=
  sheafCompose J (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1})

instance forgetSheaf_essSurj : (forgetSheaf J).EssSurj where
  mem_essImage F := by
    let e := (forget₂ (ModuleCat.{1} ℤ) AddCommGrpCat.{1}).asEquivalence
    let G := (sheafCompose J e.inverse).obj F
    refine ⟨G, ⟨(fullyFaithfulSheafToPresheaf J AddCommGrpCat.{1}).preimageIso ?_⟩⟩
    exact Functor.associator F.obj e.inverse e.functor ≪≫
      Functor.isoWhiskerLeft F.obj e.counitIso ≪≫ Functor.rightUnitor F.obj

instance forgetSheaf_isEquivalence : (forgetSheaf J).IsEquivalence where

instance forgetSheaf_additive : (forgetSheaf J).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    ext U x
    rfl

instance additiveEnoughInjectives : EnoughInjectives (Sheaf J AddCommGrpCat.{1}) :=
  IntegralComparison.AbelianSheafUniverses.enoughInjectives.{0, 1, 0} J

instance integerEnoughInjectives : EnoughInjectives (Sheaf J (ModuleCat.{1} ℤ)) :=
  EnoughInjectives.of_equivalence (forgetSheaf J)

def extEquiv [HasExt.{1} (Sheaf J (ModuleCat.{1} ℤ))]
    [HasExt.{1} (Sheaf J AddCommGrpCat.{1})]
    (M N : Sheaf J (ModuleCat.{1} ℤ)) (n : ℕ) :
    Abelian.Ext M N n ≃+
      Abelian.Ext ((forgetSheaf J).obj M) ((forgetSheaf J).obj N) n :=
  AddEquiv.ofBijective ((forgetSheaf J).mapExtAddHom M N n)
    ((forgetSheaf J).mapExt_bijective_of_preservesInjectiveObjects M N n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerSheaf.IntegerSheafEquivalence
