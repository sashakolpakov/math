import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ClassDetection
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.QuotientDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.LineNormalization

/-! # Image Line -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction

noncomputable section

/-! Descend the actual rigidified product line to the abelian Picard
image. Equality in the native Picard sheaf supplies the full descent
cocycle, and normalization preserves recovery of the original bundle. -/

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
  (hfac : uliftYoneda.map q ≫ i = SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

include βh hβh hfac in
theorem productPicard_image_fibre_class {T : Over (Spec (.of k))} (x y : T ⟶ B)
    (h : x ≫ q = y ≫ q) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line x) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line y) := by
  apply (ClassDetection.Construction.productPicard_eq_iff_class_eq D βv hβv βh hβh x y).mp
  change (SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv).app (op T) (ULift.up x) =
    (SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv).app (op T) (ULift.up y)
  rw [← hfac]
  change i.app (op T) (ULift.up (x ≫ q)) = i.app (op T) (ULift.up (y ≫ q))
  rw [h]

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]

def productPicardImageLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (C ⊗ B).left := by
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  exact D.quotientLine q (productPicard_image_fibre_class D βv hβv βh hβh q i hfac)

def productPicardImageLinePullbackIso :
    (Scheme.Modules.pullback (q ⊗ₘ 𝟙 B).left).obj
      (productPicardImageLine D βv hβv βh hβh q i hfac).sheaf ≅ D.bundle.sheaf := by
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  exact D.quotientLinePullbackIso q (productPicard_image_fibre_class D βv hβv βh hβh q i hfac)

def normalizedProductPicardImageLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (C ⊗ B).left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle B C (productPicardImageLine D βv hβv βh hβh q i hfac)

def normalizedProductPicardImageLine_axis :
    (Scheme.Modules.pullback (lift (𝟙 C) (1 : C ⟶ B)).left).obj
      (normalizedProductPicardImageLine D βv hβv βh hβh q i hfac).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule C.left :=
  FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_axis B C (productPicardImageLine D βv hβv βh hβh q i hfac)

theorem normalizedProductPicardImageLine_pullback_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 B).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 B).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle B C
      (productPicardImageLine D βv hβv βh hβh q i hfac))) = _
  rw [FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductBundle_class, FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_pullback]
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 B).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (productPicardImageLine D βv hβv βh hβh q i hfac)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle :=
    Quotient.sound ⟨productPicardImageLinePullbackIso D βv hβv βh hβh q i hfac⟩
  rw [h]
  exact FormalGeometry.Completion.Product.LineNormalization.Construction.normalizedProductClass_of_axis B B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle)
    (Quotient.sound ⟨D.axis⟩)

def normalizedProductPicardImageLinePullbackIso :
    (Scheme.Modules.pullback (q ⊗ₘ 𝟙 B).left).obj
      (normalizedProductPicardImageLine D βv hβv βh hβh q i hfac).sheaf ≅ D.bundle.sheaf :=
  Classical.choice (Quotient.exact
    (normalizedProductPicardImageLine_pullback_class D βv hβv βh hβh q i hfac))

def rigidifiedProductPicardImageLine : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B C where
  bundle := normalizedProductPicardImageLine D βv hβv βh hβh q i hfac
  axis := normalizedProductPicardImageLine_axis D βv hβv βh hβh q i hfac

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction
