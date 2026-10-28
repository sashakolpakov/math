import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.NormalizedPicardDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.AffineComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Normalized Picard Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.NormalizedPicardInjection.RelativeNormalizedPicard

noncomputable section

/-! Equality in the relative Picard sheaf identifies actual normalized
line bundles on a varying abelian family over a locally noetherian base, on arbitrary quasi-compact
quasi-separated parameters. The required isomorphism is constructed by fpqc descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {T : Over S} [CompactSpace T.left] [QuasiSeparatedSpace T.left]

theorem iso_of_picard_eq (L M : HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (eL : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj L.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule T.left)
    (eM : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj M.sheaf ≅ HilbertConstruction.Line.Bundles.structureModule T.left)
    (h : (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let R : (Scheme.fppfTopology.over S).Cover T :=
    ⟨Presheaf.equalizerSieve (F := HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme)
        (X := op T) (HilbertConstruction.Line.Bundles.LineBundle.classOf L) (HilbertConstruction.Line.Bundles.LineBundle.classOf M),
      Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
        (toSheafify (Scheme.fppfTopology.over S) (HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme)) _ _ h⟩
  have he : ∀ {U : Over S} (u : U ⟶ T), R.1 u →
      ((Scheme.Modules.pullback (u ▷ A.scheme).left).obj L.sheaf ≅
        (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M.sheaf) := by
    intro U u hu
    exact Classical.choice (Quotient.exact hu)
  obtain ⟨U, u, _, huF, huS, huQ, ⟨e⟩⟩ :=
    PELModuli.IntegralModel.Picard.AffineComparison.PicardAffineComparison.exists_affine_fpqc_comparison A.scheme L.sheaf M.sheaf R he
  let := huF
  let := huS
  let := huQ
  obtain ⟨d, _, _⟩ := NormalizedPicardDescent.RelativeNormalizedPicard.normalize_descends A u L.sheaf M.sheaf eL eM e
    L.locallyTrivial M.locallyTrivial
  exact ⟨d⟩

theorem class_eq_of_picard_eq
    (q r : HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (hq : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q = 1)
    (hr : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left r = 1)
    (h : (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) q = (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) r) :
    q = r := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep q
  obtain ⟨M, rfl⟩ := Quotient.exists_rep r
  change HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) =
    HilbertConstruction.Line.Bundles.LineBundle.classOf (HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) at hq
  change HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) =
    HilbertConstruction.Line.Bundles.LineBundle.classOf (HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) at hr
  exact Quotient.sound (iso_of_picard_eq A L M (Classical.choice (Quotient.exact hq))
    (Classical.choice (Quotient.exact hr)) h)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.NormalizedPicardInjection.RelativeNormalizedPicard
