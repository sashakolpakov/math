import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.AffineComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.NormalizedPicardDescent
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Normalized Picard Injection -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.NormalizedPicardInjection

noncomputable section

/-! Over the original field, equality in the relative Picard
sheaf determines an actual isomorphism of line bundles normalized along
zero. The parameter scheme may be nonreduced. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.NormalizedPicardDescent
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  {T : Over (Spec (.of k))} [CompactSpace T.left] [QuasiSeparatedSpace T.left]
  (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)
  (eL : (Scheme.Modules.pullback (PoincareNormalization.familyZero A T).left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)
  (eM : (Scheme.Modules.pullback (PoincareNormalization.familyZero A T).left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left)

include eL eM

/-- Equality of the sheafified classes produces an actual global
isomorphism; neither the local comparison nor its cocycle is an input. -/
theorem iso_of_picard_eq
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  let R : (Scheme.fppfTopology.over (Spec (.of k))).Cover T :=
    ⟨Presheaf.equalizerSieve (F := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme)
        (X := op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M),
      Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over (Spec (.of k)))
        (toSheafify (Scheme.fppfTopology.over (Spec (.of k)))
          (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme)) _ _ h⟩
  have he : ∀ {U : Over (Spec (.of k))} (u : U ⟶ T), R.1 u →
      ((Scheme.Modules.pullback (u ▷ A.scheme).left).obj L.sheaf ≅
        (Scheme.Modules.pullback (u ▷ A.scheme).left).obj M.sheaf) := by
    intro U u hu
    exact Classical.choice (Quotient.exact hu)
  obtain ⟨U, u, _, huF, huS, huQ, ⟨e⟩⟩ :=
    PELModuli.IntegralModel.Picard.AffineComparison.PicardAffineComparison.exists_affine_fpqc_comparison A.scheme L.sheaf M.sheaf R he
  let := huF
  let := huS
  let := huQ
  obtain ⟨d, _, _⟩ := NormalizedPicardDescent.normalize_descends A u L.sheaf M.sheaf eL eM e
    L.locallyTrivial M.locallyTrivial
  exact ⟨d⟩

theorem class_eq_of_picard_eq
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M :=
  Quotient.sound (iso_of_picard_eq A L M eL eM h)

/-- The constructed comparison can be chosen to preserve the specified
zero trivializations exactly. -/
theorem normalized_iso_of_picard_eq
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M)) :
    ∃ d : L.sheaf ≅ M.sheaf,
      (Scheme.Modules.pullback (PoincareNormalization.familyZero A T).left).map d.hom ≫ eM.hom = eL.hom := by
  obtain ⟨e⟩ := iso_of_picard_eq A L M eL eM h
  exact ⟨RigidifiedIso.normalizedIso (fst T A.scheme).left (PoincareNormalization.familyZero A T).left e eL eM,
    RigidifiedIso.normalizedIso_section (fst T A.scheme).left (PoincareNormalization.familyZero A T).left
      (PoincareNormalization.familyZero_projection A T) e eL eM⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.NormalizedPicardInjection
