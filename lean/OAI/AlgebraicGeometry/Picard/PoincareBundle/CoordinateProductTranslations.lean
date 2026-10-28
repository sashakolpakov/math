import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ProductEquivariance

/-! # Coordinate Product Translations -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations

noncomputable section

/-!
# Instantiate actual product equivariance on the canonical group-scheme coordinates
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {S : Scheme.{u}} {A B X : Over S} [GrpObj A] [GrpObj B]
  (L : Line.Bundles.LineBundle (A ⊗ X).left) (D : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L)

/-- Actual lifted coordinates satisfy the product relation whenever their group coordinates do. -/
theorem liftedRel {T : Over S} (a b c : T ⟶ A) (z : T ⟶ X) (h : a * b = c) :
    FiberwiseMultiplication.ProductRel (fst A X) (snd A X) (lift a z) (lift b z) (lift c z) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [lift_fst] using h
  · simp only [lift_snd]
  · simp only [lift_snd]

/-- The genuine product on specified actual group coordinates. -/
def productTo {T : Over S} (a b c : T ⟶ A) (z : T ⟶ X) (h : a * b = c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Line.Fibers.fiber L (lift a z)) (Line.Fibers.fiber L (lift b z)) (Line.Fibers.fiber L (lift c z)) :=
  D.product (lift a z) (lift b z) (lift c z) (liftedRel a b c z h)

variable (f : A ⟶ B) [IsMonHom f] (F : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f D)

attribute [local instance] Kernel.Scheme.kernelGroup

/-- Kernel translation is contraction by its actual normalized frame at the included group coordinate. -/
def translateTo {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (a b : T ⟶ A) (z : T ⟶ X)
    (h : (k ≫ Kernel.Scheme.kernelInclusion f) * a = b) : Line.Fibers.fiber L (lift a z) ⟶ Line.Fibers.fiber L (lift b z) :=
  Bilinear.Contraction.contractLeft (productTo L D (k ≫ Kernel.Scheme.kernelInclusion f) a b z h)
    (F.frame k (lift (k ≫ Kernel.Scheme.kernelInclusion f) z) (lift_fst _ _).symm).hom

variable [IsCommMonObj A]

/-- The product of two translated group coordinates has the combined kernel translation. -/
theorem translated_coordinates {T : Over S} (k l : T ⟶ Kernel.Scheme.kernelObject f) (x y : T ⟶ A) :
    ((k ≫ Kernel.Scheme.kernelInclusion f) * x) * ((l ≫ Kernel.Scheme.kernelInclusion f) * y) =
      ((k * l) ≫ Kernel.Scheme.kernelInclusion f) * (x * y) := by
  rw [MonObj.mul_comp]
  ac_rfl

variable (hc : KernelFrame.Centrality.Central f F)

include hc in
/-- The full product equivariance equation holds on the actual canonical kernel-translation coordinates. -/
theorem product_translations {T : Over S} (k l : T ⟶ Kernel.Scheme.kernelObject f) (x y : T ⟶ A) (z : T ⟶ X)
    (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L (lift x z), U)) (n : Γ(Line.Fibers.fiber L (lift y z), U)) :
    (productTo L D ((k ≫ Kernel.Scheme.kernelInclusion f) * x) ((l ≫ Kernel.Scheme.kernelInclusion f) * y)
      (((k * l) ≫ Kernel.Scheme.kernelInclusion f) * (x * y)) z (translated_coordinates f k l x y)).app U
      ((translateTo L D f F k x ((k ≫ Kernel.Scheme.kernelInclusion f) * x) z rfl).app U m)
      ((translateTo L D f F l y ((l ≫ Kernel.Scheme.kernelInclusion f) * y) z rfl).app U n) =
    (translateTo L D f F (k * l) (x * y) (((k * l) ≫ Kernel.Scheme.kernelInclusion f) * (x * y)) z rfl).app U
      ((productTo L D x y (x * y) z rfl).app U m n) := by
  dsimp only [translateTo]
  rw [Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app]
  exact Kernel.ProductEquivariance.product_translations (fst A X) (snd A X) f L D F hc
    k l (k * l) rfl
    (lift (k ≫ Kernel.Scheme.kernelInclusion f) z) (lift (l ≫ Kernel.Scheme.kernelInclusion f) z) (lift ((k * l) ≫ Kernel.Scheme.kernelInclusion f) z)
    (lift x z) (lift y z) (lift ((k ≫ Kernel.Scheme.kernelInclusion f) * x) z) (lift ((l ≫ Kernel.Scheme.kernelInclusion f) * y) z)
    (lift ((l ≫ Kernel.Scheme.kernelInclusion f) * x) z) (lift (x * y) z) (lift ((l ≫ Kernel.Scheme.kernelInclusion f) * (x * y)) z)
    (lift (((k * l) ≫ Kernel.Scheme.kernelInclusion f) * (x * y)) z)
    (lift_fst _ _).symm (lift_fst _ _).symm (lift_fst _ _).symm
    (liftedRel _ _ _ z rfl) (liftedRel _ _ _ z rfl)
    (liftedRel _ _ _ z (by ac_rfl)) (liftedRel _ _ _ z (mul_comm _ _)) (liftedRel _ _ _ z rfl)
    (liftedRel _ _ _ z (mul_assoc _ _ _)) (liftedRel _ _ _ z rfl) (liftedRel _ _ _ z rfl)
    (liftedRel _ _ _ z (by rw [MonObj.mul_comp, mul_assoc]))
    (liftedRel _ _ _ z (translated_coordinates f k l x y))
    (liftedRel _ _ _ z (MonObj.mul_comp k l (Kernel.Scheme.kernelInclusion f)).symm) (liftedRel _ _ _ z rfl) U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateProductTranslations
