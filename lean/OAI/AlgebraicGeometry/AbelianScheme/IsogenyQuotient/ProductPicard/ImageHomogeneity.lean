import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLineValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardDescent

/-! # Image Homogeneity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageHomogeneity.Construction

noncomputable section

/-! The actual normalized image line is homogeneous, and its native
homogeneous Picard class is exactly the original image embedding. -/

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

include βv hβv in
omit [IsAlgClosed k] [IsCommMonObj B] [IsProper B.hom] [Smooth B.hom]
  [GeometricallyIntegral B.hom] [IsLocallyNoetherian B.left] in
set_option backward.isDefEq.respectTransparency false in
theorem productPicard_bundle_homogeneous : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass B B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) := by
  have h : (SheafMap.Construction.productNativeHomogeneousClass (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv (𝟙 B)).val =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 B) ⊗ₘ 𝟙 B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) = _
    rw [tensorHom_id, id_whiskerRight, Over.id_left]
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _
  exact h ▸ (SheafMap.Construction.productNativeHomogeneousClass (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv (𝟙 B)).property

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

set_option backward.isDefEq.respectTransparency false in
theorem normalizedProductPicardImageLine_homogeneous :
    Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass B C
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) := by
  apply HomogeneousPicardDescent.Construction.homogeneousPicardClass_of_fppf_pullback B q
  change Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass B B (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 B).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)))
  rw [ImageLine.Construction.normalizedProductPicardImageLine_pullback_class]
  exact productPicard_bundle_homogeneous D βv hβv

set_option backward.isDefEq.respectTransparency false in
theorem normalizedProductPicardImageLine_native_universal_class :
    i.app (op C) (ULift.up (𝟙 C)) =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k))) (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B)).app (op C)
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac),
          normalizedProductPicardImageLine_homogeneous D βv hβv βh hβh q i hfac⟩ := by
  have : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op C)) := inferInstance
  apply (CategoryTheory.mono_iff_injective _).mp this
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.homogeneousPicardSheafInclusion_toSheafify B) (op C))
    (show (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf B).obj (op C) from
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac),
        normalizedProductPicardImageLine_homogeneous D βv hβv βh hβh q i hfac⟩)
  exact (ImageLineValue.Construction.normalizedProductPicardImageLine_universal_class D βv hβv βh hβh q i hfac).symm.trans h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageHomogeneity.Construction
