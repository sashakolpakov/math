import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.AugmentationNaturality

/-! # Cech Cone Factorization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechConeFactorization.SemilatticeCechConeFactorization

noncomputable section

/-! A natural coefficient cone on a category with a greatest element is
determined by its value there, through the canonical Čech augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u w v z
variable (C : Type u) [SemilatticeInf C] [OrderTop C]
  {ι : Type w} (U : ι → C)
  {A : Type v} [Category.{z} A] [Preadditive A] [HasProducts.{w} A] [HasZeroObject A]
  (P : Cᵒᵖ ⥤ A) (M : A) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

omit [Preadditive A] [HasProducts.{w} A] [HasZeroObject A] in
theorem cone : (Functor.const Cᵒᵖ).map (η.app (op ⊤)) ≫ CechAugmentation.SemilatticeCechAugmentation.cone C P = η := by
  apply NatTrans.ext
  funext V
  change η.app (op ⊤) ≫ P.map (homOfLE (le_top : V.unop ≤ ⊤)).op = η.app V
  exact (η.naturality (homOfLE (le_top : V.unop ≤ ⊤)).op).symm.trans (Category.id_comp _)

theorem augmentation : NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P M η =
    (CochainComplex.single₀ A).map (η.app (op ⊤)) ≫ CechAugmentation.SemilatticeCechAugmentation.augmentation C U P := by
  change _ = (CochainComplex.single₀ A).map (η.app (op ⊤)) ≫
    NonemptyCech.Augmentation.NonemptyCechAugmentation.augmentation U P (P.obj (op ⊤)) (CechAugmentation.SemilatticeCechAugmentation.cone C P)
  rw [NonemptyCech.AugmentationNaturality.NonemptyCechAugmentationNaturality.source, cone]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.CechConeFactorization.SemilatticeCechConeFactorization
