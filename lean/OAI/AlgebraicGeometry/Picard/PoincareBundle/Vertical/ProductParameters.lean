import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes

/-! # Product Parameters -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters

noncomputable section

/-!
# Actual parameter schemes and quotient squares for the vertical biextension product
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} (A X : Over S)

/-- The first vertical input on the genuine scheme with one fixed coordinate and two group coordinates. -/
def inputLeft : A ⊗ (X ⊗ X) ⟶ A ⊗ X :=
  lift (fst A (X ⊗ X)) (snd A (X ⊗ X) ≫ fst X X)

/-- The second vertical input on the same actual parameter scheme. -/
def inputRight : A ⊗ (X ⊗ X) ⟶ A ⊗ X :=
  lift (fst A (X ⊗ X)) (snd A (X ⊗ X) ≫ snd X X)

variable [GrpObj X]

/-- The vertical output multiplies the two second coordinates. -/
def outputPoint : A ⊗ (X ⊗ X) ⟶ A ⊗ X :=
  lift (fst A (X ⊗ X)) ((snd A (X ⊗ X) ≫ fst X X) * (snd A (X ⊗ X) ≫ snd X X))

/-- The universal vertical parameter points satisfy the actual vertical product relation. -/
theorem productRelation : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) (inputLeft A X) (inputRight A X) (outputPoint A X) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [inputLeft, inputRight, outputPoint, lift_snd]
  · simp only [inputLeft, inputRight, lift_fst]
  · simp only [inputLeft, outputPoint, lift_fst]

variable (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)

/-- Evaluating the genuine vertical multiplication gives its global sheaf product. -/
def globalProduct : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Line.Fibers.fiber L (inputLeft A X)) (Line.Fibers.fiber L (inputRight A X)) (Line.Fibers.fiber L (outputPoint A X)) :=
  D.product (inputLeft A X) (inputRight A X) (outputPoint A X) (productRelation A X)

/-- The universal vertical product is a bilinear line-bundle isomorphism. -/
theorem globalProduct_isIso : IsIso (Bilinear.BilinearPullback.toHom (globalProduct A X L D)) :=
  D.product_isIso _ _ _ _

/-- The universal vertical relation remains valid after every change of test scheme. -/
theorem parameterRelation {T : Over S} (a : T ⟶ A ⊗ (X ⊗ X)) :
    FiberwiseMultiplication.ProductRel (snd A X) (fst A X) (a ≫ inputLeft A X) (a ≫ inputRight A X) (a ≫ outputPoint A X) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Category.assoc, inputLeft, inputRight, outputPoint, lift_snd, MonObj.comp_mul]
  · simp only [Category.assoc, inputLeft, inputRight, lift_fst]
  · simp only [Category.assoc, inputLeft, outputPoint, lift_fst]

/-- The global vertical product recovers all its fiber products by actual geometric pullback. -/
theorem globalProduct_pullback {T : Over S} (a : T ⟶ A ⊗ (X ⊗ X)) :
    Line.Fibers.pullBilinear L a (inputLeft A X) (inputRight A X) (outputPoint A X)
      (a ≫ inputLeft A X) (a ≫ inputRight A X) (a ≫ outputPoint A X) rfl rfl rfl (globalProduct A X L D) =
      D.product (a ≫ inputLeft A X) (a ≫ inputRight A X) (a ≫ outputPoint A X) (parameterRelation A X a) :=
  D.product_natural a _ _ _ (productRelation A X) _ _ _ (parameterRelation A X a) rfl rfl rfl

variable {A X} {B Y : Over S} [GrpObj Y] (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom g]

omit [GrpObj X] [GrpObj Y] [IsMonHom g] in
/-- The first vertical input square commutes with the actual product quotient cover. -/
theorem inputLeft_naturality : (f ⊗ₘ (g ⊗ₘ g)) ≫ inputLeft B Y = inputLeft A X ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [inputLeft, Category.assoc]

omit [GrpObj X] [GrpObj Y] [IsMonHom g] in
/-- The second vertical input square commutes with the same quotient cover. -/
theorem inputRight_naturality : (f ⊗ₘ (g ⊗ₘ g)) ≫ inputRight B Y = inputRight A X ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [inputRight, Category.assoc]

/-- A group homomorphism also makes the vertical output square commute. -/
theorem outputPoint_naturality : (f ⊗ₘ (g ⊗ₘ g)) ≫ outputPoint B Y = outputPoint A X ≫ (f ⊗ₘ g) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [outputPoint, Category.assoc, MonObj.comp_mul, MonObj.mul_comp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters
