import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Universal.PicardFaithfullyFlat
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift

/-! # Fpqc Homogeneous Picard -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcHomogeneousPicard.Construction

noncomputable section

/-! Homogeneity of actual Picard classes descends through arbitrary
faithfully flat quasi-compact parameter covers, using universal source
functions to compare their normalized line bundles. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false in
theorem universal_relativePicard_eq_of_fpqc_restriction
    {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme)
    {T U : Over S} (u : U ⟶ T) [Flat u.left] [Surjective u.left] [QuasiCompact u.left]
    (c d : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (op T))
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map u.op
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) c) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.map u.op
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) d)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) c =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) d := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep c
  obtain ⟨M, rfl⟩ := Quotient.exists_rep d
  apply Universal.PicardFaithfullyFlat.Construction.universal_relativePicard_eq_of_faithfullyFlat A hA u L M
  exact (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
    (h.trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A.scheme u (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)))

set_option backward.isDefEq.respectTransparency false in
theorem homogeneousPicardClass_of_fpqc_pullback
    {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (hA : GlobalFunctions.Construction.HasUniversalGlobalFunctions A.scheme)
    {B C : Over S} (q : B ⟶ C) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (c : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).obj (op C))
    (hc : A.IsHomogeneousPicardClass B ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map q.op c)) :
    A.IsHomogeneousPicardClass C c := by
  intro U f a
  let V := pullback f q
  let p : V ⟶ U := pullback.fst f q
  let x : V ⟶ B := pullback.snd f q
  have hx : p ≫ f = x ≫ q := pullback.condition
  have hp := (IsPullback.of_hasPullback f q).map (Over.forget S)
  change IsPullback p.left x.left f.left q.left at hp
  have : Flat p.left := MorphismProperty.of_isPullback (P := @Flat) hp.flip inferInstance
  have : Surjective p.left := MorphismProperty.of_isPullback (P := @Surjective) hp.flip inferInstance
  have : QuasiCompact p.left := MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  apply universal_relativePicard_eq_of_fpqc_restriction A hA p
  rw [← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).naturality_apply,
    ← (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).naturality_apply]
  have ht := A.translationClass_naturality p a ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op c)
  have hm : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map p.op
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map f.op c) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map x.op
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map q.op c) := by
    rw [← Functor.map_comp_apply, ← op_comp, hx, op_comp, Functor.map_comp_apply]
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op V)) ht).trans
    ((congrArg (fun z => (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op V)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation (p ≫ a)).left z)) hm).trans
        ((hc V x (p ≫ a)).trans
          (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op V)) hm.symm)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FpqcHomogeneousPicard.Construction
