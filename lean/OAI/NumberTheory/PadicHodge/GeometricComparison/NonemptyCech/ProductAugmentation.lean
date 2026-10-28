import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Augmentation

/-! # Product Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductAugmentation.NonemptyCechProductAugmentation

noncomputable section

/-! Reindexing a nonempty Cech family through a product-preserving functor
preserves the canonical augmentation of the original coefficient cone. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe w v vD vA u uD uA
variable {A : Type uA} [Category.{vA} A] [HasProducts.{w} A]
  {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) {ι : Type w} (U : ι → C)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (P : Dᵒᵖ ⥤ A) (M : A) (η : (Functor.const Dᵒᵖ).obj M ⟶ P)

theorem restriction (n : SimplexCategory) :
    (Augmentation.NonemptyCechAugmentation.restriction U (F.op ⋙ P) M (Functor.whiskerLeft F.op η)).app n ≫
      ((ProductBaseChange.NonemptyCechProductBaseChange.cosimplicialIso F U P).app n).hom =
        (Augmentation.NonemptyCechAugmentation.restriction (F.obj ∘ U) P M η).app n := by
  change Pi.lift (fun t : Fin (n.len + 1) → ι => η.app (op (F.obj (∏ᶜ (U ∘ t))))) ≫
      (Pi.mapIso (fun t : Fin (n.len + 1) → ι => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)).hom =
    Pi.lift (fun t : Fin (n.len + 1) → ι => η.app (op (∏ᶜ (fun i => F.obj (U (t i))))))
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.lift_comp_π_assoc]
  erw [Pi.lift_comp_π]
  exact (η.naturality (PreservesProduct.iso F (U ∘ t)).symm.op.hom).symm.trans (Category.id_comp _)

variable [Preadditive A] [HasZeroObject A]

theorem augmentation :
    Augmentation.NonemptyCechAugmentation.augmentation U (F.op ⋙ P) M (Functor.whiskerLeft F.op η) ≫
      (ProductBaseChange.NonemptyCechProductBaseChange.complexIso F U P).hom =
        Augmentation.NonemptyCechAugmentation.augmentation (F.obj ∘ U) P M η := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, Augmentation.NonemptyCechAugmentation.augmentation_zero,
    Augmentation.NonemptyCechAugmentation.augmentation_zero]
  exact restriction F U P M η ⦋0⦌

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductAugmentation.NonemptyCechProductAugmentation
