import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafExtension

/-! # Constant Coefficient Paste -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientPaste.ConstantCoefficientUnit

noncomputable section

/-! The coefficient adjunction on constant sheaves is normalized by one fixed map of coefficient modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientCo.SheafCoefficientAdjunction OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientUnit.ConstantCoefficientExtension

private theorem paste {A B : Type*} [Category* A] [Category* B] (F : B ⥤ A)
    {X Y : A} {Z W T V Q : B}
    (a : X ⟶ Y) (b : Y ⟶ F.obj W) (u : X ⟶ F.obj Z)
    (c : Z ⟶ W) (d : W ⟶ T) (e : T ⟶ Q) (v : Z ⟶ V) (w : V ⟶ Q)
    (h : a ≫ b = u ≫ F.map c) (k : c ≫ d ≫ e = v ≫ w) :
    a ≫ b ≫ F.map d ≫ F.map e = (u ≫ F.map v) ≫ F.map w := by
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    k, Functor.map_comp, Category.assoc]

variable (R : Type 1) [Field R] [CharZero R]

def coefficientUnit : ModuleCat.of ℤ (ULift.{1} ℤ) ⟶
    (SheafCoefficientCo.SheafCoefficientAdjunction.restrictCoefficients R).obj (ModuleCat.of R R) :=
  (SheafCoefficientCo.SheafCoefficientAdjunction.coefficientAdjunction R).unit.app (ModuleCat.of ℤ (ULift.{1} ℤ)) ≫
    (SheafCoefficientCo.SheafCoefficientAdjunction.restrictCoefficients R).map (ConstantCoefficientUnit.ConstantCoefficientExtension.unitIso R).hom

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)

def sheafUnit : (constantSheaf J (ModuleCat.{1} ℤ)).obj (ModuleCat.of ℤ (ULift.{1} ℤ)) ⟶
    (SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf R J).obj ((constantSheaf J (ModuleCat.{1} R)).obj (ModuleCat.of R R)) :=
  (SheafCoefficientCo.SheafCoefficientAdjunction.adjunction R J).unit.app _ ≫ (SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf R J).map (ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).hom

omit [CharZero R] in
theorem generator :
    toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of ℤ (ULift.{1} ℤ))) ≫ (sheafUnit R J).hom =
      (Functor.const Cᵒᵖ).map (coefficientUnit R) ≫
        Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R)))
          (SheafCoefficientCo.SheafCoefficientAdjunction.restrictCoefficients R) := by
  let P := (Functor.const Cᵒᵖ).obj (ModuleCat.of ℤ (ULift.{1} ℤ))
  let Q := (Functor.const Cᵒᵖ).obj (ModuleCat.of R R)
  let I := (constantSheaf J (ModuleCat.{1} ℤ)).obj (ModuleCat.of ℤ (ULift.{1} ℤ))
  let F := SheafCoefficientCo.SheafCoefficientAdjunction.restrictCoefficients R
  let G := SheafCoefficientCo.SheafCoefficientAdjunction.extendCoefficients R
  apply NatTrans.ext
  funext U
  have hu := congr_app (Sheaf.adjunction_unit_app_hom J (SheafCoefficientCo.SheafCoefficientAdjunction.coefficientAdjunction R) I) U
  have hn := (SheafCoefficientCo.SheafCoefficientAdjunction.coefficientAdjunction R).unit.naturality ((toSheafify J P).app U)
  change (toSheafify J P).app U ≫ (SheafCoefficientCo.SheafCoefficientAdjunction.coefficientAdjunction R).unit.app (I.obj.obj U) =
    (SheafCoefficientCo.SheafCoefficientAdjunction.coefficientAdjunction R).unit.app (ModuleCat.of ℤ (ULift.{1} ℤ)) ≫
      F.map (G.map ((toSheafify J P).app U)) at hn
  have he := congr_app (SheafExtension.SheafExtensionGenerators.constant_generator R J) U
  change G.map ((toSheafify J P).app U) ≫ (toSheafify J (I.obj ⋙ G)).app U ≫
    (ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).hom.hom.app U = 𝟙 _ ≫ (ConstantCoefficientUnit.ConstantCoefficientExtension.unitIso R).hom ≫ (toSheafify J Q).app U at he
  rw [Category.id_comp] at he
  change (toSheafify J P).app U ≫ ((SheafCoefficientCo.SheafCoefficientAdjunction.adjunction R J).unit.app I).hom.app U ≫
      F.map ((ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).hom.hom.app U) =
    coefficientUnit R ≫ F.map ((toSheafify J Q).app U)
  erw [hu]
  change (toSheafify J P).app U ≫ (SheafCoefficientCo.SheafCoefficientAdjunction.coefficientAdjunction R).unit.app (I.obj.obj U) ≫
    F.map ((toSheafify J (I.obj ⋙ G)).app U) ≫ F.map ((ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).hom.hom.app U) = _
  exact paste F ((toSheafify J P).app U)
    ((SheafCoefficientCo.SheafCoefficientAdjunction.coefficientAdjunction R).unit.app (I.obj.obj U))
    ((SheafCoefficientCo.SheafCoefficientAdjunction.coefficientAdjunction R).unit.app (ModuleCat.of ℤ (ULift.{1} ℤ)))
    (G.map ((toSheafify J P).app U)) ((toSheafify J (I.obj ⋙ G)).app U)
    ((ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).hom.hom.app U) (ConstantCoefficientUnit.ConstantCoefficientExtension.unitIso R).hom ((toSheafify J Q).app U) hn he

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientPaste.ConstantCoefficientUnit
