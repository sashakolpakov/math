import OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveSheaf
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtFunctoriality

/-! # Additive Cohomology Formula -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveCohomologyFormula.AdditiveSheafCohomology

noncomputable section

/-! A single exact-functor formula for the constructed field-to-additive cohomology comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

open OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientCo.SheafCoefficientAdjunction OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerSheaf.IntegerSheafEquivalence OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantCoefficientUnit.ConstantCoefficientExtension

variable (R : Type 1) [Field R] [CharZero R]
  {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C)
  [HasExt.{1} (Sheaf J (ModuleCat.{1} R))]
  [HasExt.{1} (Sheaf J (ModuleCat.{1} ℤ))]
  [HasExt.{1} (Sheaf J AddCommGrpCat.{1})]

abbrev forgetField : Sheaf J (ModuleCat.{1} R) ⥤ Sheaf J AddCommGrpCat.{1} :=
  SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf R J ⋙ IntegerSheaf.IntegerSheafEquivalence.forgetSheaf J

def sourceMap : AdditiveSheaf.AdditiveSheafCohomology.additiveConstant J ⟶ (forgetField R J).obj (AdditiveSheaf.AdditiveSheafCohomology.fieldConstant R J) :=
  (ConstantCoefficientUnit.ConstantCoefficientExtension.forgetConstantIso J).inv ≫ (IntegerSheaf.IntegerSheafEquivalence.forgetSheaf J).map
    ((SheafCoefficientCo.SheafCoefficientAdjunction.adjunction R J).unit.app (AdditiveSheaf.AdditiveSheafCohomology.integerConstant J) ≫ (SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf R J).map (ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).hom)

theorem equiv_apply (N : Sheaf J (ModuleCat.{1} R)) (n : ℕ)
    (x : Ext (AdditiveSheaf.AdditiveSheafCohomology.fieldConstant R J) N n) :
    AdditiveSheaf.AdditiveSheafCohomology.equiv R J N n x =
      (Ext.mk₀ (sourceMap R J)).comp (x.mapExactFunctor (forgetField R J)) (zero_add n) := by
  let F := SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf R J
  let G := IntegerSheaf.IntegerSheafEquivalence.forgetSheaf J
  change (Ext.mk₀ (ConstantCoefficientUnit.ConstantCoefficientExtension.forgetConstantIso J).inv).comp
    (((Ext.mk₀ ((SheafCoefficientCo.SheafCoefficientAdjunction.adjunction R J).unit.app (AdditiveSheaf.AdditiveSheafCohomology.integerConstant J))).comp
      (((Ext.mk₀ (ConstantCoefficientUnit.ConstantCoefficientExtension.constantIso R J).hom).comp x (zero_add n)).mapExactFunctor F)
      (zero_add n)).mapExactFunctor G) (zero_add n) = _
  rw [PeriodInvariants.ExtFunctoriality.mapExactFunctor_compFunctor F G]
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, sourceMap, Functor.map_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveCohomologyFormula.AdditiveSheafCohomology
