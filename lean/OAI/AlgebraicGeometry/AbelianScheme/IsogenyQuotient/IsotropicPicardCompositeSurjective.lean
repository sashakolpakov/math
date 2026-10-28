import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.PicardPullback
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalPicardSheafMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardSheaf
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.VerticalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Product

/-! # Isotropic Picard Composite Surjective -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardCompositeSurjective.Construction

noncomputable section

/-! The actual isotropic quotient Picard map recovers the source
Poincare map after pullback. Local surjectivity then passes to the composite. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

universe u

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [GrpObj Z] [IsCommMonObj Z] (φ : A ⟶ Z) [IsMonHom φ]
  (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Picard.PoincareBundle.Symmetric.MultiplicativeFrames.secondMultiplication (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) e =
    Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hi : Picard.PoincareBundle.Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Picard.PoincareBundle.Symmetric.TransverseFrames.returnedFirst (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) e =
    Picard.PoincareBundle.Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)

variable (f : A ⟶ B) [IsMonHom f]
  (hker : ∀ (T : Over S) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1)
  (hlag :
    let F := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A n) (Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f)
    (Poincare.LineDescent.Construction.poincareNativeTorsionPairing φ P Dh Dv n e hv hi hh).relativeAnnihilator F = F)

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]

theorem nativeIsotropicQuotientPicard_pullback :
    uliftYoneda.map f ≫ IsotropicPicardSheaf.Construction.nativeIsotropicQuotientPicardSheafMap φ P Dh Dv n e hv hi hh f hker hlag ≫
      (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom =
        Poincare.VerticalPicardSheafMap.Construction.poincareVerticalPicardSheafMap (φ ^ n) P Dv := by
  let L := Picard.PoincareBundle.FirstBiextensionFactor.familyLine P (φ ^ n)
  let R := Picard.PoincareBundle.TorsionPairing.Poincare.descendedLine φ P Dh Dv n e hv hi hh f hker
    (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)
  let βL := Picard.PoincareBundle.Vertical.ProductParameters.globalProduct A A L (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  have hβL : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βL) :=
    Picard.PoincareBundle.Vertical.ProductParameters.globalProduct_isIso A A L (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  let hk := Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker
  let hz := Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
    (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)
  let βR := Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product (φ ^ n) P Dh Dv hi f hk e hv hh hz
  have hβR : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βR) :=
    Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product_isIso (φ ^ n) P Dh Dv hi f hk e hv hh hz
  exact ProductPicard.PicardPullback.Construction.productNativePicardSheafMap_pullback f L R
    (Poincare.LineDescent.Construction.nativeIsotropicQuotientLine_pullbackIso φ P Dh Dv n e hv hi hh f hker hlag) βL hβL βR hβR

theorem nativeIsotropicQuotientPicard_pullback_locallySurjective
    (hsource : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (Poincare.VerticalPicardSheafMap.Construction.poincareVerticalPicardSheafMap (φ ^ n) P Dv)) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (IsotropicPicardSheaf.Construction.nativeIsotropicQuotientPicardSheafMap φ P Dh Dv n e hv hi hh f hker hlag ≫
        (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom) := by
  have := hsource
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac (Scheme.fppfTopology.over S)
    (nativeIsotropicQuotientPicard_pullback φ P Dh Dv n e hv hi hh f hker hlag)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardCompositeSurjective.Construction
