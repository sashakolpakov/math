import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousLinePowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilyMaps

/-! # Field Homogeneity Family Maps -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldHomogeneityFamilyMaps.Geometric

noncomputable section

/-! Actual group maps pull back homogeneous line classes. An actual
group-scheme isomorphism reflects this original all-test property. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.FamilyMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomogeneousLinePowers

variable {k : Type} [Field k] {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))

theorem homogeneousLine_familyMap (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.scheme.left) (hq : AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass B q) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q) := by
  let U := Over.mk (𝟙 (Spec (.of k)))
  have ht := hq.familyMap f
  have hc : (AbelianModuli.HilbertConstruction.Picard.FamilyMaps.relativePicardPresheafMap f).app (.op U) (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily B U q) =
      AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q) := by
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 U ⊗ₘ f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U B.scheme).left q) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q)
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun t => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t q)
      (congrArg Over.Hom.left (tensorHom_snd (𝟙 U) f))
  change A.IsHomogeneousPicardClass U (AbelianModuli.ReferenceFamily.HomogeneousLinePowers.constantLineFamily A U (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q))
  exact (congrArg (A.IsHomogeneousPicardClass U) hc).mp ht

theorem homogeneousLine_iso_iff (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.scheme.left) :
    AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass A (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.hom.left q) ↔ AbelianModuli.ReferenceFamily.HomogeneousLinePowers.IsHomogeneousLineClass B q := by
  constructor
  · intro hq
    have ht := homogeneousLine_familyMap B A e.inv _ hq
    have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.inv.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.hom.left q) = q := by
      rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
      exact (congrArg (fun t => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass t q)
        (congrArg Over.Hom.left e.inv_hom_id)).trans (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q)
    exact hc ▸ ht
  · exact homogeneousLine_familyMap A B e.hom q

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.FieldHomogeneityFamilyMaps.Geometric
