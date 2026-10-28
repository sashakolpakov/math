import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Map
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PicardPullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.FamilyMap

/-! # Poincare Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.PoincarePullback

noncomputable section

/-! The canonical quotient-to-dual map satisfies the actual dual pullback equation. -/

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

variable {Bdual : Over S}
  (DA : (Homogeneous.homogeneousSheaf A).obj.RepresentableBy Z)
  (DB : (Homogeneous.homogeneousSheaf B).obj.RepresentableBy Bdual)
  (hP : DA.homEquiv (𝟙 Z) = Product.Map.sectionClass P
    (Vertical.ProductParameters.globalProduct Z A P Dv)
    (Vertical.ProductParameters.globalProduct_isIso Z A P Dv) (𝟙 Z))

include hP

/-- The constructed quotient map has the required actual dual pullback identity. -/
theorem representedMap_pullback :
    f ≫ Map.representedMap φ P Dh Dv hi f hφ symmetry hv hh he DB ≫
      DualMaps.representedDualMap DA DB f = φ := by
  have hrec := Product.PicardPullback.representedMap_pullback f f (FirstBiextensionFactor.familyLine P φ)
    (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (LineDescent.pullbackIso φ P Dh Dv hi f hφ symmetry hv hh he)
    (Vertical.ProductParameters.globalProduct A A (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
    (Vertical.ProductParameters.globalProduct_isIso A A (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
    (VerticalProduct.product φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product_isIso φ P Dh Dv hi f hφ symmetry hv hh he) DA DB
  exact hrec.trans (Product.FamilyMap.Family.representedMap_familyLine P φ
    (Vertical.ProductParameters.globalProduct Z A P Dv)
    (Vertical.ProductParameters.globalProduct_isIso Z A P Dv)
    (Vertical.ProductParameters.globalProduct A A (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv))
    (Vertical.ProductParameters.globalProduct_isIso A A (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv)) DA hP)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.PoincarePullback
