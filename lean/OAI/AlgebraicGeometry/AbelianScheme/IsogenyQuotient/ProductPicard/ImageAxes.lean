import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine

/-! # Image Axes -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageAxes.Construction

noncomputable section

/-! The constructed Picard image line is normalized on both identity
axes. The second normalization follows from the group law of the original
Picard map and its actual line-bundle recovery. -/

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

include βv hβv βh hβh in
set_option backward.isDefEq.respectTransparency false in
theorem productPicard_secondAxis_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : B ⟶ B) (𝟙 B)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass B.left := by
  have hz : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (1 : B ⟶ B)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (B ⊗ B).left :=
    congrArg Subtype.val ((ClassDetection.Construction.productPicard_zero_iff_actual_class D βv hβv βh hβh (1 : B ⟶ B)).mp
      (map_one (SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh B)))
  have he : (lift (𝟙 B) (𝟙 B)).left ≫ ((1 : B ⟶ B) ⊗ₘ 𝟙 B).left =
      (lift (1 : B ⟶ B) (𝟙 B)).left :=
    congrArg Over.Hom.left (by simp : lift (𝟙 B) (𝟙 B) ≫ ((1 : B ⟶ B) ⊗ₘ 𝟙 B) =
      lift (1 : B ⟶ B) (𝟙 B))
  rw [← he, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 B) (𝟙 B)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (1 : B ⟶ B))) = _
  rw [hz, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [GrpObj C] [IsMonHom q]
  [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]

set_option backward.isDefEq.respectTransparency false in
theorem normalizedProductPicardImageLine_secondAxis_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (1 : B ⟶ C) (𝟙 B)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass B.left := by
  have he : (lift (1 : B ⟶ B) (𝟙 B)).left ≫ (q ⊗ₘ 𝟙 B).left =
      (lift (1 : B ⟶ C) (𝟙 B)).left :=
    congrArg Over.Hom.left (by simp : lift (1 : B ⟶ B) (𝟙 B) ≫ (q ⊗ₘ 𝟙 B) =
      lift (1 : B ⟶ C) (𝟙 B))
  rw [← he, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ImageLine.Construction.normalizedProductPicardImageLine_pullback_class]
  exact productPicard_secondAxis_class D βv hβv βh hβh

def normalizedProductPicardImageLine_secondAxis :
    (Scheme.Modules.pullback (lift (1 : B ⟶ C) (𝟙 B)).left).obj
      (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left :=
  Classical.choice (Quotient.exact
    (normalizedProductPicardImageLine_secondAxis_class D βv hβv βh hβh q i hfac))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageAxes.Construction
