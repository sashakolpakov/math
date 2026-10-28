import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FppfSheafRestriction

/-! # Homogeneous Picard Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardDescent.Construction

noncomputable section

/-! Homogeneity of an actual family class descends from a single fppf
cover of its parameter scheme, on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A] {B C : Over S}
  (q : B ⟶ C) [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

set_option backward.isDefEq.respectTransparency false in
theorem homogeneousPicardClass_of_fppf_pullback
    (c : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op C))
    (hc : Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A B ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map q.op c)) :
    Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A C c := by
  intro U f a
  obtain ⟨V, p, x, _y, hflat, hsurj, hfp, hx, _hy⟩ := FormalGeometry.Completion.FppfPairLift.Construction.fppf_lift_pair q f f
  have : Flat p.left := hflat
  have : Surjective p.left := hsurj
  have : LocallyOfFinitePresentation p.left := hfp
  apply FppfSheafRestriction.Construction.fppfSheaf_restriction_injective p (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A)
  rw [← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).naturality_apply, ← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).naturality_apply]
  have ht := Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard.translationClass_naturality A p a ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op c)
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map p.op
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A a).left ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op c)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A (p ≫ a)).left
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map p.op ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op c)) at ht
  have hm : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map p.op ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map f.op c) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map x.op ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map q.op c) := by
    rw [← Functor.map_comp_apply, ← op_comp, hx, op_comp, Functor.map_comp_apply]
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op V)) ht).trans
    ((congrArg (fun z => (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op V)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.translation A (p ≫ a)).left z)) hm).trans
        ((hc V x (p ≫ a)).trans (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op V)) hm.symm)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.HomogeneousPicardDescent.Construction
