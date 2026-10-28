import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.NormalizedPicardDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.AffineComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Normalized Picard Injection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.NormalizedPicardInjection.RelativeNormalizedPicard

noncomputable section

/-! Equality in the relative Picard sheaf identifies actual normalized
line bundles on a varying abelian family over a reduced noetherian
parameter. The required isomorphism is constructed by fpqc descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {T : Over S} [IsReduced T.left] [IsNoetherian T.left]

theorem iso_of_picard_eq (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
    (eL : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
    (eM : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let R : (Scheme.fppfTopology.over S).Cover T :=
    ⟨Presheaf.equalizerSieve (F := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme)
        (X := op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M),
      Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
        (toSheafify (Scheme.fppfTopology.over S) (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme)) _ _ h⟩
  have he : ∀ {U : Over S} (u : U ⟶ T), R.1 u →
      ((Scheme.Modules.pullback (u ▷ A.scheme).left).obj L.sheaf ≅
        (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M.sheaf) := by
    intro U u hu
    exact Classical.choice (Quotient.exact hu)
  obtain ⟨U, u, _, huF, huS, huQ, ⟨e⟩⟩ :=
    Picard.AffineComparison.PicardAffineComparison.exists_affine_fpqc_comparison A.scheme L.sheaf M.sheaf R he
  let := huF
  let := huS
  let := huQ
  obtain ⟨d, _, _⟩ := NormalizedPicardDescent.RelativeNormalizedPicard.normalize_descends A u L.sheaf M.sheaf eL eM e
    L.locallyTrivial M.locallyTrivial
  exact ⟨d⟩

theorem class_eq_of_picard_eq
    (q r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (hq : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left q = 1)
    (hr : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left r = 1)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) q = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) r) :
    q = r := by
  obtain ⟨L, rfl⟩ := Quotient.exists_rep q
  obtain ⟨M, rfl⟩ := Quotient.exists_rep r
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) at hq
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) at hr
  exact Quotient.sound (iso_of_picard_eq A L M (Classical.choice (Quotient.exact hq))
    (Classical.choice (Quotient.exact hr)) h)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.NormalizedPicardInjection.RelativeNormalizedPicard
