import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfSheafRestriction

/-! # Image Line Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLineValue.Construction

noncomputable section

/-! The descended and normalized actual line represents the original
Picard-image embedding on every test scheme. -/

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

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

set_option backward.isDefEq.respectTransparency false in
theorem normalizedProductPicardImageLine_universal_class :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op C)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)) =
        (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op C) (i.app (op C) (ULift.up (𝟙 C))) := by
  apply FppfSheafRestriction.Construction.fppfSheaf_restriction_injective q (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B)
  rw [← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).naturality_apply]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op B)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ 𝟙 B).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac))) = _
  rw [ImageLine.Construction.normalizedProductPicardImageLine_pullback_class]
  let p := i ≫ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom
  have hn : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B).obj.map q.op (p.app (op C) (ULift.up (𝟙 C))) =
      p.app (op B) (ULift.up q) := by
    have h := (congrArg (fun t : (uliftYoneda.{u + 1}.obj C).obj (op C) ⟶
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B).obj.obj (op B) => t (ULift.up (𝟙 C))) (p.naturality q.op)).symm
    change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B).obj.map q.op (p.app (op C) (ULift.up (𝟙 C))) =
      p.app (op B) (ULift.up (q ≫ 𝟙 C)) at h
    simpa only [Category.comp_id] using h
  change _ = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B).obj.map q.op (p.app (op C) (ULift.up (𝟙 C)))
  rw [hn]
  have hf := congrArg (fun t : uliftYoneda.{u + 1}.obj B ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj =>
    t.app (op B) (ULift.up (𝟙 B))) hfac
  change i.app (op B) (ULift.up ((𝟙 B) ≫ q)) =
    SheafMap.Construction.productNativePicardSectionHom (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh B (𝟙 B) at hf
  rw [Category.id_comp] at hf
  change _ = (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op B) (i.app (op B) (ULift.up q))
  rw [hf, ← Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply, RelativeValue.Construction.productPicard_relativeValue]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op B) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op B)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 B) ⊗ₘ 𝟙 B).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle))
  rw [tensorHom_id, id_whiskerRight, Over.id_left]
  exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op B))
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.bundle)).symm

set_option backward.isDefEq.respectTransparency false in
theorem normalizedProductPicardImageLine_family_value {T : Over (Spec (.of k))} (x : T ⟶ C) :
    (ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).relativeValue x =
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) (i.app (op T) (ULift.up x)) := by
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (x ⊗ₘ 𝟙 B).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac))) = _
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T)
    ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map x.op
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac))) = _
  rw [(AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).naturality_apply, normalizedProductPicardImageLine_universal_class]
  let p := i ≫ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom
  have h := (congrArg (fun t : (uliftYoneda.{u + 1}.obj C).obj (op C) ⟶
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B).obj.obj (op T) => t (ULift.up (𝟙 C))) (p.naturality x.op)).symm
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B).obj.map x.op (p.app (op C) (ULift.up (𝟙 C))) =
    p.app (op T) (ULift.up (x ≫ 𝟙 C)) at h
  rw [Category.comp_id] at h
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B).obj.map x.op (p.app (op C) (ULift.up (𝟙 C))) =
    p.app (op T) (ULift.up x)
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLineValue.Construction
