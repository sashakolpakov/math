import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex

/-! # Reindex Opens -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ReindexOpens

noncomputable section

/-! Reindexing homogeneous variables pulls standard projective opens
back to the corresponding actual coordinate opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex

universe u
variable (R : CommRingCat.{u}) {σ : Type u} {n : ℕ} (e : σ ≃ Fin (n + 1))

theorem e33ProjectiveReindex_preimage_basicOpen (i : Fin (n + 1)) :
    (AbelianModuli.HilbertConstruction.Projective.SpaceReindex.affineProjectiveSpaceReindexIso R e).hom.left ⁻¹ᵁ
      Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X i) =
        Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X (e.symm i)) := by
  have h := Proj.map_preimage_basicOpen (AbelianModuli.HilbertConstruction.Polynomial.Reindex.polynomialReindexGraded R e.symm)
    (AbelianModuli.HilbertConstruction.Polynomial.Reindex.polynomialReindexGraded_irrelevant R e.symm) (X i)
  exact h.trans (congrArg (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (rename_X e.symm i))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ReindexOpens
