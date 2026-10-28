import OAI.RepresentationTheory.Theta.Geometric.Normalized.SquareZeroDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection

/-! # Picard Reflection -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.PicardReflection

noncomputable section

/-! Equality of normalized Picard classes after the nonflat parameter
map reflects back to the actual original line-bundle classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
theorem squareZero_normalized_picard_eq_reflects
    {V R S : Type} [AddCommGroup V] [Module ℂ V] [Module ℂᵐᵒᵖ V] [IsCentralScalar ℂ V]
    [CommRing R] [Algebra ℂ R] [Nontrivial R] [CommRing S] [Algebra ℂ S] [Nontrivial S]
    (i : V →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (q : R →ₐ[ℂ] S) (he : Function.Exact i q.toLinearMap)
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V) ⊗ A.scheme).left)
    (eL : (Scheme.Modules.pullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V))).left).obj L.sheaf ≅
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V)).left)
    (eN : (Scheme.Modules.pullback (AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization.familyZero A
      (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V))).left).obj N.sheaf ≅
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ V)).left)
    (h : (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R))
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (Normalized.SquareZeroDescent.complexSquareZeroParameterMap i hsq ▷ A.scheme).left)) =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R))
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (N.pullback (Normalized.SquareZeroDescent.complexSquareZeroParameterMap i hsq ▷ A.scheme).left))) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf N := by
  let u := Normalized.SquareZeroDescent.complexSquareZeroParameterMap i hsq
  have : CompactSpace (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left := inferInstanceAs (CompactSpace (Spec (.of R)))
  have : QuasiSeparatedSpace (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R).left := inferInstanceAs (QuasiSeparatedSpace (Spec (.of R)))
  obtain ⟨e⟩ := AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection.NormalizedPicard.iso_of_picard_eq A (L.pullback (u ▷ A.scheme).left)
    (N.pullback (u ▷ A.scheme).left)
    (AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.localZeroIso A u L.sheaf eL)
    (AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardLocal.NormalizedPicard.localZeroIso A u N.sheaf eN) h
  obtain ⟨d, _, _⟩ := Normalized.SquareZeroDescent.normalized_squareZero_iso_descends i hi hsq q he A L.sheaf N.sheaf
    L.locallyTrivial N.locallyTrivial eL eN e
  exact Quotient.sound ⟨d⟩

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.PicardReflection
