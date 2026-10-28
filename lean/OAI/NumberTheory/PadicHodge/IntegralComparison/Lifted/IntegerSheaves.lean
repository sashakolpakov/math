import Mathlib

/-! # Integer Sheaves -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheaves

noncomputable section

/-!
# IntegralComparison: lifted-integer module sheaves are abelian sheaves

The coefficient ring is lifted into the same universe as the module
values. Restriction along the actual ring equivalence with the integers
followed by the native integer-module equivalence preserves higher Ext.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u t

abbrev Integers : Type u := ULift.{u} ℤ

abbrev coefficientForget : ModuleCat.{u} Integers ⥤ AddCommGrpCat.{u} :=
  ModuleCat.restrictScalars (ULift.ringEquiv : Integers ≃+* ℤ).symm.toRingHom ⋙
    forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}

instance coefficientForget_isEquivalence : coefficientForget.{u}.IsEquivalence := by
  infer_instance

instance coefficientForget_leftAdjoint : coefficientForget.{u}.IsLeftAdjoint :=
  coefficientForget.{u}.asEquivalence.isLeftAdjoint_functor

instance coefficientForget_rightAdjoint : coefficientForget.{u}.IsRightAdjoint :=
  coefficientForget.{u}.asEquivalence.symm.isRightAdjoint_inverse

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

abbrev sheafForget : Sheaf J (ModuleCat.{u + 1} Integers) ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  sheafCompose J coefficientForget

instance sheafForget_essSurj : (sheafForget.{u} J).EssSurj where
  mem_essImage F := by
    let e := coefficientForget.{u + 1}.asEquivalence
    let G := (sheafCompose J e.inverse).obj F
    refine ⟨G, ⟨(fullyFaithfulSheafToPresheaf J AddCommGrpCat.{u + 1}).preimageIso ?_⟩⟩
    exact Functor.associator F.obj e.inverse e.functor ≪≫
      Functor.isoWhiskerLeft F.obj e.counitIso ≪≫ Functor.rightUnitor F.obj

instance sheafForget_isEquivalence : (sheafForget.{u} J).IsEquivalence where

instance sheafForget_leftAdjoint : (sheafForget.{u} J).IsLeftAdjoint :=
  (sheafForget.{u} J).asEquivalence.isLeftAdjoint_functor

instance sheafForget_rightAdjoint : (sheafForget.{u} J).IsRightAdjoint :=
  (sheafForget.{u} J).asEquivalence.symm.isRightAdjoint_inverse

instance sheafForget_additive : (sheafForget.{u} J).Additive where
  map_add := by
    intro M N a b
    apply Sheaf.hom_ext
    ext U x
    rfl

variable [HasSheafify J (ModuleCat.{u + 1} Integers)] [HasSheafify J AddCommGrpCat.{u + 1}]

def constantUnitIso :
    (sheafForget.{u} J).obj
        ((constantSheaf J (ModuleCat.{u + 1} Integers)).obj (ModuleCat.of Integers Integers)) ≅
      (constantSheaf J AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (constantCommuteCompose J coefficientForget).app (ModuleCat.of Integers Integers)

variable [HasExt.{t} (Sheaf J (ModuleCat.{u + 1} Integers))]
  [HasExt.{t} (Sheaf J AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf J (ModuleCat.{u + 1} Integers))]

def extEquiv (M N : Sheaf J (ModuleCat.{u + 1} Integers)) (n : ℕ) :
    Abelian.Ext.{t} M N n ≃+
      Abelian.Ext.{t} ((sheafForget J).obj M) ((sheafForget J).obj N) n :=
  AddEquiv.ofBijective ((sheafForget J).mapExtAddHom M N n)
    ((sheafForget J).mapExt_bijective_of_preservesInjectiveObjects M N n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheaves
