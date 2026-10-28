import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.BaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Augmentation

/-! # Base Change Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.BaseChangeAugmentation.NonemptyCechBaseChangeAugmentation

noncomputable section

/-! The actual Čech base-change isomorphism preserves the canonical
augmentation of a naturally restricted coefficient cone. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v u' v' w z t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type u'} [Category.{v'} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type w} [Category.{z} A] [Preadditive A] [HasProducts.{t} A] [HasZeroObject A]
  (F : C ⥤ D) [PreservesFiniteLimits F] {ι : Type t} (U : ι → C) (P : Dᵒᵖ ⥤ A)

omit [HasZeroObject A] in
theorem hom_zero : (BaseChange.NonemptyCechBaseChange.complexIso F U P).hom.f 0 =
    (BaseChange.NonemptyCechBaseChange.componentIso F U P ⦋0⦌).hom := rfl

variable (M : A) (η : (Functor.const Dᵒᵖ).obj M ⟶ P)

theorem augmentation :
    Augmentation.NonemptyCechAugmentation.augmentation U (F.op ⋙ P) M (Functor.whiskerLeft F.op η) ≫
      (BaseChange.NonemptyCechBaseChange.complexIso F U P).hom =
    Augmentation.NonemptyCechAugmentation.augmentation (F.obj ∘ U) P M η := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, Augmentation.NonemptyCechAugmentation.augmentation_zero,
    Augmentation.NonemptyCechAugmentation.augmentation_zero, hom_zero]
  change Pi.lift (fun t : Fin 1 → ι => η.app (op (F.obj (∏ᶜ (U ∘ t))))) ≫
      (Pi.mapIso (fun t : Fin 1 → ι => P.mapIso (PreservesProduct.iso F (U ∘ t)).symm.op)).hom =
    Pi.lift (fun t : Fin 1 → ι => η.app (op (∏ᶜ (fun j => F.obj (U (t j))))))
  apply Pi.hom_ext
  intro t
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.lift_comp_π_assoc]
  erw [Pi.lift_comp_π]
  exact (η.naturality (PreservesProduct.iso F (U ∘ t)).symm.op.hom).symm.trans (Category.id_comp _)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.BaseChangeAugmentation.NonemptyCechBaseChangeAugmentation
