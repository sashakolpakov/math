import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Coproduct Matrix Components -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents

noncomputable section

/-! Components determine maps between finite coproducts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteBiproducts C]

def finiteCoproductProjection {ι : Type w} [Fintype ι] (M : ι → C) (i : ι) :
    (∐ M) ⟶ M i := (biproduct.isoCoproduct M).inv ≫ biproduct.π M i

theorem finiteCoproductProjection_hom_ext {ι : Type w} [Fintype ι] (M : ι → C)
    {N : C} {f g : N ⟶ ∐ M}
    (h : ∀ i, f ≫ finiteCoproductProjection M i = g ≫ finiteCoproductProjection M i) : f = g := by
  apply (cancel_mono (biproduct.isoCoproduct M).inv).mp
  apply biproduct.hom_ext
  intro i
  exact (Category.assoc _ _ _).trans ((h i).trans (Category.assoc _ _ _).symm)

theorem finiteCoproduct_matrix_ext {ι κ : Type w} [Fintype ι] [Fintype κ]
    (M : ι → C) (N : κ → C) {f g : (∐ M) ⟶ ∐ N}
    (h : ∀ i j,
      Sigma.ι M i ≫ f ≫ finiteCoproductProjection N j =
        Sigma.ι M i ≫ g ≫ finiteCoproductProjection N j) : f = g := by
  apply Sigma.hom_ext
  intro i
  apply finiteCoproductProjection_hom_ext N
  intro j
  exact (Category.assoc _ _ _).trans ((h i j).trans (Category.assoc _ _ _).symm)

def finiteCoproductEncodedMatrix {ι κ : Type w} [Fintype ι] [Fintype κ]
    (M : ι → C) (N : κ → C) {P : κ → ι → Type*}
    (e : ∀ j i, (M i ⟶ N j) ≃ P j i) (f : (∐ M) ⟶ ∐ N) : ∀ j i, P j i :=
  fun j i => e j i (Sigma.ι M i ≫ f ≫ finiteCoproductProjection N j)

theorem finiteCoproductEncodedMatrix_injective {ι κ : Type w} [Fintype ι] [Fintype κ]
    (M : ι → C) (N : κ → C) {P : κ → ι → Type*}
    (e : ∀ j i, (M i ⟶ N j) ≃ P j i) :
    Function.Injective (finiteCoproductEncodedMatrix M N e) := by
  intro f g h
  apply finiteCoproduct_matrix_ext M N
  intro i j
  apply (e j i).injective
  exact congrArg (fun a => a j i) h

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents
