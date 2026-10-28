import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.LineDescent
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.VerticalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Product

/-! # Isotropic Picard Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardSheaf.Construction

noncomputable section

/-! Construct the quotient-to-Picard-sheaf homomorphism from the actual
Poincare descent data and the scheme-theoretic self-annihilating kernel. -/

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

/-- The actual isotropic quotient line defines a map to the native Picard sheaf
without supplying a representing dual scheme. -/
def nativeIsotropicQuotientPicardSheafMap :
    uliftYoneda.{u + 1}.obj B ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj :=
  ProductPicard.SheafMap.Construction.productNativePicardSheafMap
    (Picard.PoincareBundle.TorsionPairing.Poincare.descendedLine φ P Dh Dv n e hv hi hh f hker
      (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag))
    (Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product (φ ^ n) P Dh Dv hi f
      (Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
      (Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
        (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)))
    (Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product_isIso (φ ^ n) P Dh Dv hi f
      (Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
      (Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
        (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)))

variable [IsLocallyNoetherian ((B ⊗ B) ⊗ B).left]

/-- On every test scheme, the constructed map is a homomorphism. -/
def nativeIsotropicQuotientPicardSectionHom (T : Over S) :
    (T ⟶ B) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (.op T) :=
  ProductPicard.SheafMap.Construction.productNativePicardSectionHom
    (Picard.PoincareBundle.TorsionPairing.Poincare.descendedLine φ P Dh Dv n e hv hi hh f hker
      (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag))
    (Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product (φ ^ n) P Dh Dv hi f
      (Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
      (Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
        (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)))
    (Picard.PoincareBundle.CanonicalPoincare.VerticalProduct.product_isIso (φ ^ n) P Dh Dv hi f
      (Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
      (Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
        (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)))
    (Picard.PoincareBundle.CanonicalPoincare.Product.product (φ ^ n) P Dh Dv hi f
      (Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
      (Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
        (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag)))
    (Picard.PoincareBundle.CanonicalPoincare.Product.product_isIso (φ ^ n) P Dh Dv hi f
      (Picard.PoincareBundle.Poincare.TorsionKernelFrame.multiple_annihilates_kernel f φ n hker) e hv hh
      (Picard.PoincareBundle.TorsionPairing.Poincare.kernel_isotropic φ P Dh Dv n e hv hi hh f hker
        (Poincare.LineDescent.Construction.poincareNativeKernel_selfAnnihilating φ P Dh Dv n e hv hi hh f hker hlag))) T

theorem nativeIsotropicQuotientPicardSectionHom_apply (T : Over S) (x : T ⟶ B) :
    nativeIsotropicQuotientPicardSectionHom φ P Dh Dv n e hv hi hh f hker hlag T x =
      (nativeIsotropicQuotientPicardSheafMap φ P Dh Dv n e hv hi hh f hker hlag).app
        (.op T) (ULift.up x) := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsotropicPicardSheaf.Construction
