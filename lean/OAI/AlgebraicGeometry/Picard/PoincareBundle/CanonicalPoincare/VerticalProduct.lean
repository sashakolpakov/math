import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.VerticalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CentralFrames

/-! # Vertical Product -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.VerticalProduct

noncomputable section

/-!
# The genuine Poincare vertical product descends through the isotropic kernel

The kernel frames, their centrality and transverse laws, the quotient line, and the quotient
product are all constructed from the original Poincare data and scheme-theoretic annihilation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters

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
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]

/-- The canonical descended Poincare line has its actual globally descended vertical product. -/
def product :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
      ((LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he).pullback (Vertical.ProductParameters.inputLeft B B).left).sheaf
      ((LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he).pullback (Vertical.ProductParameters.inputRight B B).left).sheaf
      ((LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he).pullback (Vertical.ProductParameters.outputPoint B B).left).sheaf :=
  Isotropic.VerticalProduct.product f f (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ)
    (LineDescent.secondKernelFrames φ P Dh Dv f hφ symmetry hv) (Poincare.TransverseFrames.source_interchange φ P Dh Dv hi)
    (LineDescent.transverse_frames φ P Dh Dv hi f hφ symmetry hv hh) he (Poincare.CentralFrames.second_central φ P Dh f hφ Dv symmetry hv)

/-- This canonical descended Poincare product is an actual line-bundle isomorphism. -/
theorem product_isIso : IsIso (Bilinear.BilinearPullback.toHom (product φ P Dh Dv hi f hφ symmetry hv hh he)) :=
  Isotropic.VerticalProduct.product_isIso f f (FirstBiextensionFactor.familyLine P φ)
    (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv) (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ)
    (LineDescent.secondKernelFrames φ P Dh Dv f hφ symmetry hv) (Poincare.TransverseFrames.source_interchange φ P Dh Dv hi)
    (LineDescent.transverse_frames φ P Dh Dv hi f hφ symmetry hv hh) he (Poincare.CentralFrames.second_central φ P Dh f hφ Dv symmetry hv)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.VerticalProduct
