import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.SecondUnitFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent

/-! # Second Unit Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.SecondUnitFrame

noncomputable section

/-!
# The normalized unit on the actual canonical descended Poincare line
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralParameterScheme

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hi : Biextension.Compatibility.Interchange P Dh Dv) (f : A ⟶ B) [IsMonHom f] (hφ : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) symmetry = Poincare.TransverseFrames.sourceVertical φ P Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) symmetry =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
  (he : Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv)
    f f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ) (LineDescent.secondKernelFrames φ P Dh Dv f hφ symmetry hv))
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian B.left]

/-- The canonical quotient Poincare line carries its actual normalized vertical unit frame. -/
def unitFrame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left ≅
    ((LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he).pullback (SecondNeutralParameterScheme.point B B).left).sheaf :=
  Isotropic.SecondUnitFrame.unitFrame f f (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ)
    (LineDescent.secondKernelFrames φ P Dh Dv f hφ symmetry hv) (Poincare.TransverseFrames.source_interchange φ P Dh Dv hi)
    (LineDescent.transverse_frames φ P Dh Dv hi f hφ symmetry hv hh) he

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.SecondUnitFrame
