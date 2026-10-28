import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Products -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Products.CM.Abelian

noncomputable section

/-!
Actual fourfold products for CMAbelianVariety. The binary construction uses the scheme
fiber product, the Segre closed immersion, and native product group laws.
No product-existence or cycle-algebraicity hypothesis is introduced here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

section Cartesian

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def fourCartesianProjection (X : Fin 4 → C) :
    ∀ i : Fin 4, (X 0 ⊗ X 1) ⊗ (X 2 ⊗ X 3) ⟶ X i := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))))
  · exact fst _ _ ≫ fst _ _
  · exact fst _ _ ≫ snd _ _
  · exact snd _ _ ≫ fst _ _
  · exact snd _ _ ≫ snd _ _

@[simp] theorem fourCartesianProjection_zero (X : Fin 4 → C) :
    fourCartesianProjection X 0 = fst _ _ ≫ fst (X 0) (X 1) := rfl

@[simp] theorem fourCartesianProjection_one (X : Fin 4 → C) :
    fourCartesianProjection X 1 = fst _ _ ≫ snd (X 0) (X 1) := rfl

@[simp] theorem fourCartesianProjection_two (X : Fin 4 → C) :
    fourCartesianProjection X 2 = snd _ _ ≫ fst (X 2) (X 3) := rfl

@[simp] theorem fourCartesianProjection_three (X : Fin 4 → C) :
    fourCartesianProjection X 3 = snd _ _ ≫ snd (X 2) (X 3) := rfl

def fourCartesianIsLimit (X : Fin 4 → C) :
    IsLimit (Fan.mk ((X 0 ⊗ X 1) ⊗ (X 2 ⊗ X 3))
      (fourCartesianProjection X)) := by
  refine Fan.IsLimit.mk _ (fun s =>
    lift (lift (s.proj 0) (s.proj 1)) (lift (s.proj 2) (s.proj 3))) ?_ ?_
  · intro s i
    fin_cases i <;> simp [Fan.proj]
  · intro s m h
    apply CartesianMonoidalCategory.hom_ext
    · apply CartesianMonoidalCategory.hom_ext
      · simpa [Category.assoc] using h 0
      · simpa [Category.assoc] using h 1
    · apply CartesianMonoidalCategory.hom_ext
      · simpa [Category.assoc] using h 2
      · simpa [Category.assoc] using h 3

end Cartesian

def fourProduct (A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety :=
  Albanese.Construction.SegreClosed.abelianProduct (Albanese.Construction.SegreClosed.abelianProduct (A 0) (A 1))
    (Albanese.Construction.SegreClosed.abelianProduct (A 2) (A 3))

def fourProjection (A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    ∀ i : Fin 4, (fourProduct A).toOver ⟶ (A i).toOver :=
  fourCartesianProjection (fun i => (A i).toOver)

/-- The fourfold abelian variety is a product in schemes over `Spec ℂ`. -/
def fourProductIsLimit (A : Fin 4 → ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    IsLimit (Fan.mk (fourProduct A).toOver (fourProjection A)) :=
  fourCartesianIsLimit (fun i => (A i).toOver)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Products.CM.Abelian
