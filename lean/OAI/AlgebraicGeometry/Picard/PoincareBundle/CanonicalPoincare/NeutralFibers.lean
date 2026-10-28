import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.UnitFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.FiberFrames

/-! # Neutral Fibers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.NeutralFibers

noncomputable section

/-!
# Actual natural unit frames on all neutral quotient Poincare fibers
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.ParameterScheme

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

/-- The constructed quotient unit gives a genuine unit frame at every neutral quotient test point. -/
def frame {T : Over S} (a : T ⟶ B ⊗ B) (ha : a ≫ fst B B = 1) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he) a :=
  Neutral.FiberFrames.frame (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (UnitFrame.unitFrame φ P Dh Dv hi f hφ symmetry hv hh he) a ha

/-- The canonical quotient unit frames commute with every change of test scheme. -/
theorem frame_natural {T U : Over S} (t : U ⟶ T) (a : T ⟶ B ⊗ B) (a' : U ⟶ B ⊗ B)
    (ha : a ≫ fst B B = 1) (ha' : a' ≫ fst B B = 1) (hta : t ≫ a = a') :
    Line.Fibers.pullSection (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he) t a a' hta
      (frame φ P Dh Dv hi f hφ symmetry hv hh he a ha).hom =
    (frame φ P Dh Dv hi f hφ symmetry hv hh he a' ha').hom :=
  Neutral.FiberFrames.frame_natural (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (UnitFrame.unitFrame φ P Dh Dv hi f hφ symmetry hv hh he) t a a' ha ha' hta

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.NeutralFibers
