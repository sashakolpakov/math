import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplicationIso
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames

/-! # Multiplicative Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames

noncomputable section

/-!
# Construct the second multiplicative kernel-frame system from actual symmetry

Coordinate exchange, geometric pullback, and the given symmetry of the line construct the
second multiplication and all of its kernel-frame laws from the first system.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (L : Line.Bundles.LineBundle (A ⊗ A).left)
  (D : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) L)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj L.sheaf ≅ L.sheaf)

/-- Exchange the coordinates in the actual first multiplication. -/
def exchangedMultiplication : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) (L.pullback (β_ A A).hom.left) :=
  MultiplicationCoordinates.congrCoordinates
    (FiberwiseMultiplicationPullback.pullbackMultiplication (fst A A) (snd A A)
      (β_ A A).hom L D) (braiding_hom_fst A A) (braiding_hom_snd A A)

/-- Actual symmetry transports the exchanged multiplication onto the original line bundle. -/
def secondMultiplication : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) L :=
  FiberwiseMultiplicationIso.transportMultiplication (snd A A) (fst A A)
    (L.pullback (β_ A A).hom.left) L symmetry (exchangedMultiplication L D)

variable (f : A ⟶ B) [IsMonHom f] (F : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) L f D)

/-- The complete first kernel-frame system pulls back through coordinate exchange. -/
def exchangedFrames : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) (L.pullback (β_ A A).hom.left) f
    (exchangedMultiplication L D) :=
  Kernel.FramesPullback.congrCoordinates f (L.pullback (β_ A A).hom.left)
    (FiberwiseMultiplicationPullback.pullbackMultiplication (fst A A) (snd A A) (β_ A A).hom L D)
    (Kernel.FramesPullback.pullbackFrames (fst A A) (snd A A) (β_ A A).hom f L D F)
    (braiding_hom_fst A A) (braiding_hom_snd A A)

/-- The second full multiplicative kernel-frame system is constructed using genuine symmetry. -/
def secondFrames : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) L f (secondMultiplication L D symmetry) :=
  FiberwiseMultiplicationIso.transportKernelFrames (snd A A) (fst A A)
    (L.pullback (β_ A A).hom.left) L symmetry (exchangedMultiplication L D) f
    (exchangedFrames L D f F)

variable {Z : Over S} [GrpObj Z] [IsCommMonObj A] [IsCommMonObj Z]
  (φ : A ⟶ Z) [IsMonHom φ]
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (DP : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P)

/-- Scheme-theoretic torsion containment and actual Poincare symmetry construct the second system. -/
def multipleSecondFrames (n : ℕ)
    (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
    (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj
      (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
      (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf) :
    FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) (FirstBiextensionFactor.familyLine P (φ ^ n)) f
      (secondMultiplication _ (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P DP) e) :=
  secondFrames _ (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P DP) e f
    (Pulled.KernelFrames.Poincare.multipleKernelFrames φ P DP f n hker)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
