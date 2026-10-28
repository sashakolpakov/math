import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FiberProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesFromNeutral
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TorsionKernelFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Kernel Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare

noncomputable section

/-!
# Construct the complete multiplicative Poincare kernel-frame system without a splitting hypothesis

The input is the actual normalized fiberwise multiplication of the Poincare line. Pullback,
neutral-fiber normalization, and scheme-theoretic annihilation construct the kernel frames and
prove their unit, multiplicativity, and geometric naturality laws.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {A B Z X : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ]
  (P : Line.Bundles.LineBundle (Z ⊗ X).left)
  (D : FiberwiseMultiplication.Multiplication (fst Z X) (snd Z X) P)

/-- The actual pulled-back multiplication is presented in the image of the source group coordinate. -/
def imageMultiplication : FiberwiseMultiplication.Multiplication (fst A X ≫ φ) (snd A X) (FirstBiextensionFactor.familyLine P φ) :=
  MultiplicationCoordinates.congrCoordinates (FiberwiseMultiplicationPullback.pullbackMultiplication (fst Z X) (snd Z X)
    (φ ⊗ₘ 𝟙 X) P D) (tensorHom_fst φ (𝟙 X))
    ((tensorHom_snd φ (𝟙 X)).trans (Category.comp_id (snd A X)))

omit [GrpObj A] [IsMonHom φ] in
/-- The genuine Poincare coordinate product has coherent normalized neutral frames after pullback. -/
theorem imageMultiplication_neutral : MultiplicationCoordinates.NeutralProducts (imageMultiplication φ P D) := by
  have : Mono (lift (fst Z X) (snd Z X)) := by rw [lift_fst_snd]; infer_instance
  apply MultiplicationCoordinates.congrCoordinates_neutral
  intro T a b c ha hb hc h U
  exact Neutral.FiberProducts.pullback_unitFrame_product (fst Z X) (snd Z X) P D (φ ⊗ₘ 𝟙 X)
    a b c ha hb hc h U

/-- Restrict the actual image-coordinate multiplication to the original source group coordinate. -/
def sourceMultiplication : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) (FirstBiextensionFactor.familyLine P φ) :=
  MultiplicationCoordinateMap.restrictCoordinate (fst A X) (snd A X) φ (FirstBiextensionFactor.familyLine P φ)
    (imageMultiplication φ P D)

variable (f : A ⟶ B) [IsMonHom f] (hφ : Kernel.Scheme.kernelInclusion f ≫ φ = 1)

/-- Annihilation of the actual subgroup constructs its complete multiplicative kernel-frame system. -/
def kernelFrames : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) (FirstBiextensionFactor.familyLine P φ) f (sourceMultiplication φ P D) :=
  Kernel.FramesFromNeutral.kernelFrames (fst A X) (snd A X) f φ hφ (FirstBiextensionFactor.familyLine P φ)
    (imageMultiplication φ P D) (imageMultiplication_neutral φ P D)

variable [IsCommMonObj A] [IsCommMonObj Z]

/-- Torsion containment constructs the full multiplicative frame system of the multiple Poincare line in every characteristic. -/
def multipleKernelFrames (n : ℕ)
    (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1) :
    FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) (FirstBiextensionFactor.familyLine P (φ ^ n)) f (sourceMultiplication (φ ^ n) P D) :=
  kernelFrames (φ ^ n) P D f (Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
