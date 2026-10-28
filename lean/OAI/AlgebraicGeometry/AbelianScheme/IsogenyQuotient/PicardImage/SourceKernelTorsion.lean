import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedPullbackKernelTorsion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.FamilyTorsionDetection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceKernelValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageMultiplication

/-! # Source Kernel Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceKernelTorsion.Construction

noncomputable section

/-! On every affine locally noetherian parameter, the actual image-to-source
Picard map has kernel killed by an exponent of the original quotient kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable [GrpObj C] [IsMonHom q]

variable [Mono i]
  {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (DA : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac

include D βv hβv βh hβh q hfac in
set_option backward.isDefEq.respectTransparency false in
theorem picardImageSourceKernel_affine_torsion
    {T : Over (Spec (.of k))} [IsAffine T.left] [IsLocallyNoetherian T.left]
    (x : T ⟶ C) (hx : x ≫ SourceMap.Construction.picardImageSourceMap DA f i = 1)
    (n : ℕ) (hn : ∀ (U : Over (Spec (.of k))) (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), z ^ n = 1) :
    x ^ n = 1 := by
  let H := ProductPicard.ImageGroup.Construction.productPicardImageSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh q i hfac T
  have hH : Function.Injective H := by
    intro a b hab
    have hm : Mono (i.app (op T)) := inferInstance
    exact ULift.up_injective ((CategoryTheory.mono_iff_injective _).mp hm hab)
  have hv := ProductPicard.ImageLineValue.Construction.normalizedProductPicardImageLine_family_value D βv hβv βh hβh q i hfac x
  have hz := SourceKernelValue.Construction.picardImageSourceKernel_relative_zero DA f i x hx
  have hrel : (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((Q).line x))) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
    exact (congrArg ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)) hv).trans hz
  exact Picard.FamilyTorsionDetection.Construction.picardFamily_point_torsion H hH x ((Q).line x) hv n
    (RigidifiedPullbackKernelTorsion.Construction.rigidifiedLine_pullback_kernel_torsion f ((Q).line x) ((Q).frame x) hrel n hn)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SourceKernelTorsion.Construction
