import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.SheafCoefficientAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSheafUniverses

/-! # Integer Sheaf Equivalence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntegerSheafEquivalence.IntegralIntegerSheafEquivalence

noncomputable section

/-! Integer-module sheaves and additive sheaves have the same actual Ext groups on small sites. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type} [Category.{0} C] (J : GrothendieckTopology C)

abbrev forgetSheaf : Sheaf J (ModuleCat.{0} ℤ) ⥤ Sheaf J AddCommGrpCat.{0} :=
  sheafCompose J (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0})

instance forgetSheaf_essSurj : (forgetSheaf J).EssSurj where
  mem_essImage F := by
    let e := (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).asEquivalence
    let G := (sheafCompose J e.inverse).obj F
    refine ⟨G, ⟨(fullyFaithfulSheafToPresheaf J AddCommGrpCat.{0}).preimageIso ?_⟩⟩
    exact Functor.associator F.obj e.inverse e.functor ≪≫
      Functor.isoWhiskerLeft F.obj e.counitIso ≪≫ Functor.rightUnitor F.obj

instance forgetSheaf_isEquivalence : (forgetSheaf J).IsEquivalence where

instance forgetSheaf_additive : (forgetSheaf J).Additive where
  map_add := by
    intro M N f g
    apply Sheaf.hom_ext
    ext U x
    rfl

instance additiveEnoughInjectives : EnoughInjectives (Sheaf J AddCommGrpCat.{0}) :=
  IntegralComparison.AbelianSheafUniverses.enoughInjectives.{0, 0, 0} J

instance integerEnoughInjectives : EnoughInjectives (Sheaf J (ModuleCat.{0} ℤ)) :=
  EnoughInjectives.of_equivalence (forgetSheaf J)

universe w w'

def extEquiv [HasExt.{w} (Sheaf J (ModuleCat.{0} ℤ))]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{0})]
    (M N : Sheaf J (ModuleCat.{0} ℤ)) (n : ℕ) :
    Abelian.Ext.{w} M N n ≃+
      Abelian.Ext.{w'} ((forgetSheaf J).obj M) ((forgetSheaf J).obj N) n :=
  AddEquiv.ofBijective ((forgetSheaf J).mapExtAddHom M N n)
    ((forgetSheaf J).mapExt_bijective_of_preservesInjectiveObjects M N n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntegerSheafEquivalence.IntegralIntegerSheafEquivalence
