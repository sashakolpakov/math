import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartCechContraction
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.AugmentationNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.BaseChangeAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechConeFactorization

/-! # Subchart Cech Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartCechAugmentation.SemilatticeSubchartCechAugmentation

noncomputable section

/-! The local Čech comparison preserves the original natural cone and
factors its augmentation through the actual coefficient on the chosen chart. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u w v z
variable (C : Type u) [SemilatticeInf C] {ι : Type w} (U : ι → C) (I : C)
  {A : Type v} [Category.{z} A] [Preadditive A] [HasProducts.{w} A] [HasZeroObject A]
  (P : Cᵒᵖ ⥤ A) (M : A) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

def restrictedCone : (Functor.const (Set.Iic I)ᵒᵖ).obj M ⟶
    SubchartCechContraction.SemilatticeSubchartCechContraction.coefficients C I P :=
  Functor.whiskerLeft (MeetRestriction.SemilatticeMeetRestriction.inclusion C I).op η

omit [Preadditive A] [HasProducts.{w} A] [HasZeroObject A] in
theorem meet_cone : η ≫ MeetRestriction.SemilatticeMeetRestriction.comparison C I P =
    Functor.whiskerLeft (MeetRestriction.SemilatticeMeetRestriction.restriction C I).op
      (restrictedCone C I P M η) := by
  apply NatTrans.ext
  funext V
  change η.app V ≫ P.map (homOfLE (inf_le_left : V.unop ⊓ I ≤ V.unop)).op =
    η.app (op (V.unop ⊓ I))
  exact (η.naturality (homOfLE (inf_le_left : V.unop ⊓ I ≤ V.unop)).op).symm.trans (Category.id_comp _)

variable (h : ∀ V : C, IsIso (P.map (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))

theorem comparison : NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P M η ≫
    (SubchartCechContraction.SemilatticeSubchartCechContraction.complexIso C U I P h).hom =
  NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation (SubchartCechContraction.SemilatticeSubchartCechContraction.family C U I)
    (SubchartCechContraction.SemilatticeSubchartCechContraction.coefficients C I P) M (restrictedCone C I P M η) := by
  change NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P M η ≫
      (IntegralComparison.NonemptyCechNerve.complexFunctor U).map (MeetRestriction.SemilatticeMeetRestriction.comparison C I P) ≫
        (NonemptyCech.BaseChange.NonemptyCechBaseChange.complexIso (MeetRestriction.SemilatticeMeetRestriction.restriction C I) U
          (SubchartCechContraction.SemilatticeSubchartCechContraction.coefficients C I P)).hom = _
  erw [← Category.assoc, NonemptyCech.AugmentationNaturality.NonemptyCechAugmentationNaturality.coefficients, meet_cone]
  exact NonemptyCech.BaseChangeAugmentation.NonemptyCechBaseChangeAugmentation.augmentation
    (MeetRestriction.SemilatticeMeetRestriction.restriction C I) U
    (SubchartCechContraction.SemilatticeSubchartCechContraction.coefficients C I P) M (restrictedCone C I P M η)

theorem factorization : NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P M η ≫
    (SubchartCechContraction.SemilatticeSubchartCechContraction.complexIso C U I P h).hom =
  (CochainComplex.single₀ A).map (η.app (op I)) ≫
    CechAugmentation.SemilatticeCechAugmentation.augmentation (Set.Iic I)
      (SubchartCechContraction.SemilatticeSubchartCechContraction.family C U I) (SubchartCechContraction.SemilatticeSubchartCechContraction.coefficients C I P) :=
  (comparison C U I P M η h).trans
    (CechConeFactorization.SemilatticeCechConeFactorization.augmentation (Set.Iic I)
      (SubchartCechContraction.SemilatticeSubchartCechContraction.family C U I) (SubchartCechContraction.SemilatticeSubchartCechContraction.coefficients C I P)
      M (restrictedCone C I P M η))

theorem homotopy_factorization (i : ι) (hi : I ≤ U i) : NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P M η =
    (CochainComplex.single₀ A).map (η.app (op I)) ≫
      (SubchartCechContraction.SemilatticeSubchartCechContraction.homotopyEquiv C U I P h i hi).hom := by
  apply (cancel_mono (SubchartCechContraction.SemilatticeSubchartCechContraction.complexIso C U I P h).hom).mp
  rw [factorization]
  change _ = ((CochainComplex.single₀ A).map (η.app (op I)) ≫
    ((CechContraction.SemilatticeCechContraction.homotopyEquiv (Set.Iic I)
      (SubchartCechContraction.SemilatticeSubchartCechContraction.family C U I) i
      (SubchartCechContraction.SemilatticeSubchartCechContraction.family_self C U I i hi)
      (SubchartCechContraction.SemilatticeSubchartCechContraction.coefficients C I P)).hom ≫
        (SubchartCechContraction.SemilatticeSubchartCechContraction.complexIso C U I P h).inv)) ≫
      (SubchartCechContraction.SemilatticeSubchartCechContraction.complexIso C U I P h).hom
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    CechAugmentation.SemilatticeCechAugmentation.hom_eq]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.SubchartCechAugmentation.SemilatticeSubchartCechAugmentation
