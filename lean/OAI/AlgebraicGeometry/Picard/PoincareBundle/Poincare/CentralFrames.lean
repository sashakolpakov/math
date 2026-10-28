import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Centrality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent

/-! # Central Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CentralFrames

noncomputable section

/-!
# Centrality of both constructed Poincare kernel-frame systems

Centrality follows from the actual Poincare unit laws before pullback. No commutativity of an
unconstructed quotient multiplication is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [GrpObj B] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P)

omit [GrpObj A] [IsMonHom φ] in
/-- The normalized Poincare unit remains central in its actual image-coordinate multiplication. -/
theorem image_central : Neutral.FrameCentrality.NeutralCentral (Pulled.KernelFrames.Poincare.imageMultiplication φ P Dh) := by
  have : Mono (lift (fst Z A) (snd Z A)) := by rw [lift_fst_snd]; infer_instance
  apply Neutral.FrameCentrality.congrCoordinates
  apply Neutral.FrameCentrality.pullback
  exact Neutral.FrameCentrality.neutral_central Dh

variable (f : A ⟶ B) [IsMonHom f] (hf : Kernel.Scheme.kernelInclusion f ≫ φ = 1)

/-- The first actual Poincare kernel frames are central by scheme-theoretic annihilation and the genuine unit laws. -/
theorem first_central : KernelFrame.Centrality.Central f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) := by
  intro T k a x y ha hax hxa U m
  exact image_central φ P Dh T a x y
    (Kernel.FramesFromNeutral.kernel_point_neutral (fst A A) f φ hf k a ha)
    (MultiplicationCoordinateMap.mappedRel (fst A A) (snd A A) φ a x y hax)
    (MultiplicationCoordinateMap.mappedRel (fst A A) (snd A A) φ x a y hxa) U m

variable (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) e = TransverseFrames.sourceVertical φ P Dv)

/-- Actual product-exchanging symmetry proves centrality of the constructed second kernel frames. -/
theorem second_central : KernelFrame.Centrality.Central f (CanonicalPoincare.LineDescent.secondKernelFrames φ P Dh Dv f hf e hv) :=
  KernelFrame.Centrality.compatible_second_central (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
    e f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hf) (TransverseFrames.sourceVertical φ P Dv) hv (first_central φ P Dh f hf)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CentralFrames
