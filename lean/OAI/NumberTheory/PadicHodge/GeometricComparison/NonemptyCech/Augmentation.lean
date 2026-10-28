import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve
import Mathlib.Algebra.Homology.Single

/-! # Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Augmentation.NonemptyCechAugmentation

noncomputable section

/-! A natural coefficient cone gives the canonical augmentation into the
original nonempty-tuple Čech cochain complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w z t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Preadditive A] [HasProducts.{t} A] [HasZeroObject A]
  {ι : Type t} (U : ι → C) (P : Cᵒᵖ ⥤ A) (M : A) (η : (Functor.const Cᵒᵖ).obj M ⟶ P)

def cosimplicial : CosimplicialObject A :=
  (FormalCoproduct.cosimplicialObjectFunctor (IntegralComparison.NonemptyCechNerve.nerve U)).obj P

def restriction : (Functor.const SimplexCategory).obj M ⟶ cosimplicial U P where
  app n := Pi.lift (fun i => η.app (op (((IntegralComparison.NonemptyCechNerve.nerve U).obj (op n)).obj i)))
  naturality n m f := by
    let En := (IntegralComparison.NonemptyCechNerve.nerve U).obj (op n)
    let Em := (IntegralComparison.NonemptyCechNerve.nerve U).obj (op m)
    let φ : Em ⟶ En := (IntegralComparison.NonemptyCechNerve.nerve U).map f.op
    change 𝟙 M ≫ Pi.lift (fun i : Em.I => η.app (op (Em.obj i))) =
      Pi.lift (fun i : En.I => η.app (op (En.obj i))) ≫
        Pi.lift (fun i : Em.I => Pi.π (fun j : En.I => P.obj (op (En.obj j))) (φ.f i) ≫
          P.map (φ.φ i).op)
    apply Pi.hom_ext
    intro i
    simp only [Category.id_comp, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    exact (Category.id_comp _).symm.trans (η.naturality (φ.φ i).op)

omit [HasZeroObject A] in
theorem cocycle : (restriction U P M η).app ⦋0⦌ ≫
    ((IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P).d 0 1 = 0 := by
  let a := restriction U P M η
  let Y := cosimplicial U P
  have hd : (AlgebraicTopology.AlternatingCofaceMapComplex.obj Y).d 0 1 =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD Y 0 :=
    CochainComplex.of_d (fun n : ℕ => Y.obj ⦋n⦌) (AlgebraicTopology.AlternatingCofaceMapComplex.objD Y) 0
  change a.app ⦋0⦌ ≫ (AlgebraicTopology.AlternatingCofaceMapComplex.obj Y).d 0 1 = 0
  rw [hd]
  change a.app ⦋0⦌ ≫ (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • Y.map (SimplexCategory.δ i)) = 0
  simp only [Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul, Fin.val_one,
    pow_one, neg_smul, one_smul, Preadditive.comp_add, Preadditive.comp_neg]
  have h0 : a.app ⦋1⦌ = a.app ⦋0⦌ ≫ Y.map (SimplexCategory.δ (0 : Fin 2)) :=
    (Category.id_comp _).symm.trans (a.naturality (SimplexCategory.δ (0 : Fin 2)))
  have h1 : a.app ⦋1⦌ = a.app ⦋0⦌ ≫ Y.map (SimplexCategory.δ (1 : Fin 2)) :=
    (Category.id_comp _).symm.trans (a.naturality (SimplexCategory.δ (1 : Fin 2)))
  rw [← h0, ← h1, add_neg_cancel]

def augmentation : (CochainComplex.single₀ A).obj M ⟶ (IntegralComparison.NonemptyCechNerve.complexFunctor U).obj P :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨(restriction U P M η).app ⦋0⦌, cocycle U P M η⟩

theorem augmentation_zero : (augmentation U P M η).f 0 = (restriction U P M η).app ⦋0⦌ :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.Augmentation.NonemptyCechAugmentation
