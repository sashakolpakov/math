import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Double Complex Augmentation -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex

noncomputable section

/-!
# The column-zero augmentation into the actual total complex

An augmentation into the zeroth column of a first-quadrant double complex
induces a cochain map into its total complex when the first horizontal
differential kills it. The construction uses the native total-complex
inclusions and the actual horizontal-plus-signed-vertical differential.
No exactness or quasi-isomorphism is assumed here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v

variable {R : Type u} [Ring R]
variable (K : HomologicalComplex₂ (ModuleCat.{v} R)
  (ComplexShape.up ℕ) (ComplexShape.up ℕ))
variable {A : CochainComplex (ModuleCat.{v} R) ℕ}
variable (ε : A ⟶ K.X 0)

/-- The horizontal augmentation identity holds in every vertical degree. -/
theorem augmentation_horizontal_zero (hε : ε ≫ K.d 0 1 = 0) (n : ℕ) :
    ε.f n ≫ (K.d 0 1).f n = 0 := by
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
    congrArg (fun f : A ⟶ K.X 1 => f.f n) hε

/-- The actual map into total degree `n`, supported in bidegree `(0,n)`. -/
def augmentationComponent (n : ℕ) : A.X n ⟶ (K.total (ComplexShape.up ℕ)).X n :=
  ε.f n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp)

/-- The component maps commute with the total differential. At column zero
the vertical sign is one, and the horizontal summand vanishes. -/
theorem augmentationComponent_comm (hε : ε ≫ K.d 0 1 = 0) (n : ℕ) :
    augmentationComponent K ε n ≫ (K.total (ComplexShape.up ℕ)).d n (n + 1) =
      A.d n (n + 1) ≫ augmentationComponent K ε (n + 1) := by
  dsimp only [augmentationComponent]
  rw [Category.assoc, DoubleComplexSigns.DoubleComplex.iota_d_of_eq]
  simp only [pow_zero, one_smul, comp_add]
  rw [← Category.assoc, augmentation_horizontal_zero K ε hε n, zero_comp, zero_add]
  rw [← Category.assoc, ε.comm, Category.assoc]

/-- An augmentation of the zeroth column induces a genuine cochain map to
the native first-quadrant total complex. -/
def augmentationToTotal (hε : ε ≫ K.d 0 1 = 0) : A ⟶ K.total (ComplexShape.up ℕ) where
  f := augmentationComponent K ε
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact augmentationComponent_comm K ε hε i

variable (hε : ε ≫ K.d 0 1 = 0)

/-- In each degree the augmentation lands in the zeroth-column summand. -/
@[simp]
theorem augmentationToTotal_f (n : ℕ) :
    (augmentationToTotal K ε hε).f n =
      ε.f n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) := rfl

/-- The cochain-map identity holds for arbitrary degree pairs, including
the pairs whose differentials are forced to vanish by the complex shape. -/
@[reassoc]
theorem augmentationToTotal_comm (i j : ℕ) :
    (augmentationToTotal K ε hε).f i ≫ (K.total (ComplexShape.up ℕ)).d i j =
      A.d i j ≫ (augmentationToTotal K ε hε).f j :=
  (augmentationToTotal K ε hε).comm i j

/-- Projection back to column zero recovers the given augmentation exactly. -/
@[reassoc (attr := simp)]
theorem augmentationToTotal_πTotal_zero (n : ℕ) :
    (augmentationToTotal K ε hε).f n ≫ DoubleComplexProjections.DoubleComplex.πTotal K 0 n n (Nat.zero_add n) = ε.f n := by
  rw [augmentationToTotal_f, Category.assoc, DoubleComplexProjections.DoubleComplex.iota_πTotal_self, Category.comp_id]

/-- Every positive-column projection of the augmentation vanishes. -/
@[reassoc]
theorem augmentationToTotal_πTotalOrZero_ne (n p q : ℕ) (hp : p ≠ 0) :
    (augmentationToTotal K ε hε).f n ≫ DoubleComplexProjections.DoubleComplex.πTotalOrZero K p q n = 0 := by
  have hne : (0, n) ≠ (p, q) := by
    intro h
    exact hp (congrArg Prod.fst h).symm
  rw [augmentationToTotal_f, Category.assoc,
    DoubleComplexProjections.DoubleComplex.iota_πTotalOrZero_ne K 0 n p q n (Nat.zero_add n) hne, comp_zero]

/-- Elementwise form of the zeroth-column component identity. -/
@[simp]
theorem πTotal_augmentationToTotal_apply (n : ℕ) (x : A.X n) :
    DoubleComplexProjections.DoubleComplex.πTotal K 0 n n (Nat.zero_add n) ((augmentationToTotal K ε hε).f n x) = ε.f n x :=
  congrArg (fun f : A.X n ⟶ (K.X 0).X n => f x)
    (augmentationToTotal_πTotal_zero K ε hε n)

/-- An injective augmentation remains injective in each total degree. -/
theorem augmentationToTotal_f_injective (n : ℕ) (hinj : Function.Injective (ε.f n)) :
    Function.Injective ((augmentationToTotal K ε hε).f n) := by
  intro x y h
  apply hinj
  simpa only [πTotal_augmentationToTotal_apply] using
    congrArg (DoubleComplexProjections.DoubleComplex.πTotal K 0 n n (Nat.zero_add n)) h

end

end OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexAugmentation.DoubleComplex
