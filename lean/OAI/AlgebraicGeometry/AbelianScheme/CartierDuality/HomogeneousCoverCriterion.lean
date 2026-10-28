import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FppfCoverDetection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousBaseChange

/-! # Homogeneous Cover Criterion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HomogeneousCoverCriterion.Construction.KernelCharacters

noncomputable section

/-!
# CartierDuality: fppf-local translation invariance gives genuine Picard homogeneity
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard

universe u

variable {S : Scheme.{u}} (B : Over S) [GrpObj B]

/-- Equality with a translate in the actual Picard sheaf is detected by a genuine fppf cover. -/
theorem translationInvariant_of_fppf {T U : Over S} (t : U ⟶ T)
    [Flat t.left] [Surjective t.left] [LocallyOfFinitePresentation t.left]
    (b : T ⟶ B) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ B).left)
    (hq : Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.TranslationInvariant B (t ≫ b) ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map t.op q)) :
    Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.TranslationInvariant B b q := by
  let R := fun z : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ B).left => (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (.op U) z
  apply FppfCoverDetection.Construction.Schemes.fppfSheaf_restriction_injective t (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf B)
  exact (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality B t (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation B) b).left q)).trans
    ((congrArg R (Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.translationClass_naturality B t b q)).trans
      (hq.trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality B t q).symm))

variable {B} {A : Over S} (f : A ⟶ B)
    [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

/-- It suffices to prove translation invariance for all points that lift to the fppf cover. -/
theorem homogeneous_of_liftedTranslations (T : Over S)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).obj (.op T))
    (hq : ∀ (U : Over S) (g : U ⟶ T) (a : U ⟶ A),
      Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.TranslationInvariant B (a ≫ f) ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map g.op q)) :
    Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass B T q := by
  intro U g b
  obtain ⟨V, t, a, htflat, htsurj, htfp, ha⟩ := FppfCoverDetection.Construction.KernelCharacters.exists_fppf_point_lift f b
  apply translationInvariant_of_fppf B t b ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B).map g.op q)
  have h := hq V (t ≫ g) a
  simpa only [ha, op_comp, Functor.map_comp_apply] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.HomogeneousCoverCriterion.Construction.KernelCharacters
