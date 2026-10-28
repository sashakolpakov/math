import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheaves

/-! # Small Integer -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SmallInteger.SmallIntegerSheafCoefficients

noncomputable section

/-! # Integer-module and abelian sheaves in the original small coefficient universe -/

open _root_.CategoryTheory Limits

universe u

abbrev Integers : Type u := ULift.{u} ℤ

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

abbrev forget : Sheaf J (ModuleCat.{u} Integers) ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafCompose J NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheaves.coefficientForget

instance essSurj : (forget.{u} J).EssSurj where
  mem_essImage F := by
    let e := NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheaves.coefficientForget.{u}.asEquivalence
    let G := (sheafCompose J e.inverse).obj F
    refine ⟨G, ⟨(fullyFaithfulSheafToPresheaf J AddCommGrpCat.{u}).preimageIso ?_⟩⟩
    exact Functor.associator F.obj e.inverse e.functor ≪≫
      Functor.isoWhiskerLeft F.obj e.counitIso ≪≫ Functor.rightUnitor F.obj

instance isEquivalence : (forget.{u} J).IsEquivalence where

instance additive : (forget.{u} J).Additive where
  map_add := by
    intro M N a b
    apply Sheaf.hom_ext
    ext U x
    rfl

instance leftAdjoint : (forget.{u} J).IsLeftAdjoint :=
  (forget.{u} J).asEquivalence.isLeftAdjoint_functor

instance rightAdjoint : (forget.{u} J).IsRightAdjoint :=
  (forget.{u} J).asEquivalence.symm.isRightAdjoint_inverse

variable [HasSheafify J (ModuleCat.{u} Integers)] [HasSheafify J AddCommGrpCat.{u}]

def constantIso :
    (forget.{u} J).obj ((constantSheaf J (ModuleCat.{u} Integers)).obj
      (ModuleCat.of Integers Integers)) ≅
        (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (constantCommuteCompose J NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheaves.coefficientForget).app
    (ModuleCat.of Integers Integers)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SmallInteger.SmallIntegerSheafCoefficients
