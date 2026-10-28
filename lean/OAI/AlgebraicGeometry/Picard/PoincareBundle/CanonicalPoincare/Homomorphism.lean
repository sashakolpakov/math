import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Map
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Product
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.Homomorphism

/-! # Homomorphism -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Homomorphism

noncomputable section

/-! The canonical quotient-to-dual map preserves the group law. -/

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

variable [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left]
  {Bdual : Over S} [GrpObj Bdual]
  (Q : Line.Bundles.LineBundle (Bdual ⊗ B).left)
  (Qh : FiberwiseMultiplication.Multiplication (fst Bdual B) (snd Bdual B) Q)
  (Qv : FiberwiseMultiplication.Multiplication (snd Bdual B) (fst Bdual B) Q)
  (DB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy Bdual)
  (hQ : DB.homEquiv (𝟙 Bdual) = Product.Map.sectionClass Q
    (Vertical.ProductParameters.globalProduct Bdual B Q Qv)
    (Vertical.ProductParameters.globalProduct_isIso Bdual B Q Qv) (𝟙 Bdual))

include Q Qh Qv hQ

/-- The actual canonical descended map is a group-scheme homomorphism. -/
theorem representedMap_isMonHom : IsMonHom
    (Map.representedMap φ P Dh Dv hi f hφ symmetry hv hh he DB) :=
  Product.Homomorphism.representedMap_isMonHom Q
    (Vertical.ProductParameters.globalProduct Bdual B Q Qv)
    (Vertical.ProductParameters.globalProduct_isIso Bdual B Q Qv) DB hQ
    (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product_isIso φ P Dh Dv hi f hφ symmetry hv hh he)
    (Product.product φ P Dh Dv hi f hφ symmetry hv hh he)
    (Product.product_isIso φ P Dh Dv hi f hφ symmetry hv hh he)
    (Product.ParameterSchemes.globalProduct Bdual B Q Qh)
    (Product.ParameterSchemes.globalProduct_isIso Bdual B Q Qh)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Homomorphism
