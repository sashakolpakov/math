import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.VerticalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Map

/-! # Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Map

noncomputable section

/-! Constructing the actual quotient-to-dual morphism from canonical isotropic Poincare descent. -/

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

/-- The descended line defines homogeneous actual classes under every change of test scheme. -/
theorem familyClass_isHomogeneous {T : Over S} (x : T ⟶ B) :
    Homogeneous.IsHomogeneous B T
      (Vertical.Homogeneity.familyClass (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he) x) :=
  Vertical.Homogeneity.familyClass_isHomogeneous
    (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product_isIso φ P Dh Dv hi f hφ symmetry hv hh he) x

/-- The usual homogeneous Picard universal property constructs the actual map from the quotient to its dual. -/
def representedMap {Bdual : Over S}
    (DB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy Bdual) : B ⟶ Bdual :=
  Product.Map.representedMap
    (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product_isIso φ P Dh Dv hi f hφ symmetry hv hh he) DB

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Map
