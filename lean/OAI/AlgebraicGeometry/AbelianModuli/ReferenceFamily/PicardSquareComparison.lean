import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback

/-! # Picard Square Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PicardSquareComparison

noncomputable section

/-! Actual Picard pullbacks along commuting squares and inverse
scheme isomorphisms, without extra line-bundle descent assumptions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction

theorem picardPullback_square {W X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : X ⟶ W) (d : W ⟶ Z) (h : a ≫ b = c ≫ d) (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass Z) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback a (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback b q) = Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback c (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback d q) :=
  (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp a b q).symm.trans
    ((congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q) h).trans (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp c d q))

theorem picardPullback_inverse {X Y : Scheme.{0}} (e : X ≅ Y)
    (p : HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y)
    (h : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback e.hom q = p) : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback e.inv p = q :=
  (congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback e.inv) h.symm).trans
    ((HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp e.inv e.hom q).symm.trans
      ((congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q) e.inv_hom_id).trans (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PicardSquareComparison
