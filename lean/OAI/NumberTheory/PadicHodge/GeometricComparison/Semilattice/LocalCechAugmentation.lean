import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechContraction
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.AugmentationNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.BaseChangeAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechConeFactorization

/-! # Local Cech Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechAugmentation.SemilatticeLocalCechAugmentation

noncomputable section

/-! The local Čech comparison preserves the original natural cone and
factors its augmentation through the actual coefficient on the chosen chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u w v z
variable (C : Type u) [SemilatticeInf C] {ι : Type w} (U : ι → C) (i : ι)
  {A : Type v} [Category.{z} A] [Preadditive A] [HasProducts.{w} A] [HasZeroObject A]
  (P : Cᵒᵖ ⥤ A) (M : A) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

def restrictedCone : (Functor.const (Set.Iic (U i))ᵒᵖ).obj M ⟶
    LocalCechContraction.SemilatticeLocalCechContraction.coefficients C U i P :=
  Functor.whiskerLeft (MeetRestriction.SemilatticeMeetRestriction.inclusion C (U i)).op η

omit [Preadditive A] [HasProducts.{w} A] [HasZeroObject A] in
theorem meet_cone : η ≫ MeetRestriction.SemilatticeMeetRestriction.comparison C (U i) P =
    Functor.whiskerLeft (MeetRestriction.SemilatticeMeetRestriction.restriction C (U i)).op
      (restrictedCone C U i P M η) := by
  apply NatTrans.ext
  funext V
  change η.app V ≫ P.map (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op =
    η.app (op (V.unop ⊓ U i))
  exact (η.naturality (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op).symm.trans (Category.id_comp _)

variable (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op))

theorem comparison : NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P M η ≫
    (LocalCechContraction.SemilatticeLocalCechContraction.complexIso C U i P h).hom =
  NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation (LocalCechContraction.SemilatticeLocalCechContraction.family C U i)
    (LocalCechContraction.SemilatticeLocalCechContraction.coefficients C U i P) M (restrictedCone C U i P M η) := by
  change NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P M η ≫
      (IntegralComparison.NonemptyCechNerve.complexFunctor U).map (MeetRestriction.SemilatticeMeetRestriction.comparison C (U i) P) ≫
        (NonemptyCech.BaseChange.NonemptyCechBaseChange.complexIso (MeetRestriction.SemilatticeMeetRestriction.restriction C (U i)) U
          (LocalCechContraction.SemilatticeLocalCechContraction.coefficients C U i P)).hom = _
  erw [← Category.assoc, NonemptyCech.AugmentationNaturality.NonemptyCechAugmentationNaturality.coefficients, meet_cone]
  exact NonemptyCech.BaseChangeAugmentation.NonemptyCechBaseChangeAugmentation.augmentation
    (MeetRestriction.SemilatticeMeetRestriction.restriction C (U i)) U
    (LocalCechContraction.SemilatticeLocalCechContraction.coefficients C U i P) M (restrictedCone C U i P M η)

theorem factorization : NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P M η ≫
    (LocalCechContraction.SemilatticeLocalCechContraction.complexIso C U i P h).hom =
  (CochainComplex.single₀ A).map (η.app (op (U i))) ≫
    CechAugmentation.SemilatticeCechAugmentation.augmentation (Set.Iic (U i))
      (LocalCechContraction.SemilatticeLocalCechContraction.family C U i) (LocalCechContraction.SemilatticeLocalCechContraction.coefficients C U i P) :=
  (comparison C U i P M η h).trans
    (CechConeFactorization.SemilatticeCechConeFactorization.augmentation (Set.Iic (U i))
      (LocalCechContraction.SemilatticeLocalCechContraction.family C U i) (LocalCechContraction.SemilatticeLocalCechContraction.coefficients C U i P)
      M (restrictedCone C U i P M η))

theorem homotopy_factorization : NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P M η =
    (CochainComplex.single₀ A).map (η.app (op (U i))) ≫
      (LocalCechContraction.SemilatticeLocalCechContraction.homotopyEquiv C U i P h).hom := by
  apply (cancel_mono (LocalCechContraction.SemilatticeLocalCechContraction.complexIso C U i P h).hom).mp
  rw [factorization]
  change _ = ((CochainComplex.single₀ A).map (η.app (op (U i))) ≫
    ((CechContraction.SemilatticeCechContraction.homotopyEquiv (Set.Iic (U i))
      (LocalCechContraction.SemilatticeLocalCechContraction.family C U i) i
      (LocalCechContraction.SemilatticeLocalCechContraction.family_self C U i)
      (LocalCechContraction.SemilatticeLocalCechContraction.coefficients C U i P)).hom ≫
        (LocalCechContraction.SemilatticeLocalCechContraction.complexIso C U i P h).inv)) ≫
      (LocalCechContraction.SemilatticeLocalCechContraction.complexIso C U i P h).hom
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    CechAugmentation.SemilatticeCechAugmentation.hom_eq]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.LocalCechAugmentation.SemilatticeLocalCechAugmentation
