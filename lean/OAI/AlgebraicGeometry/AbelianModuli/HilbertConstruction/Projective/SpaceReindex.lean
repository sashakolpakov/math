import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.Reindex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MapOverBase
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.GrassmannianProjectivity

/-! # Space Reindex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex

noncomputable section

/-!
Comparison of finite-coordinate projective space with HilbertConstruction's projective space
indexed by a finite ordinal, including compatibility with arbitrary bases.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {σ : Type u} {n : ℕ}

theorem degreeZeroConstants_eq_algebraMap :
    (ProjectivePresentations.degreeZeroConstants R n).toRingHom = algebraMap R (ProjectivePresentations.coordinateGrading R n 0) := by
  apply RingHom.ext
  intro r
  rfl

def affineProjectiveSpaceReindexIso (e : σ ≃ Fin (n + 1)) :
    Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R)) ≅
      ProjectivePresentations.affineProjectiveSpace R n :=
  Over.isoMk (Polynomial.Reindex.polynomialProjectiveReindexIso R e) (by
    change (Polynomial.Reindex.polynomialProjectiveReindexIso R e).hom ≫
      (Proj.toSpecZero (ProjectivePresentations.coordinateGrading R n) ≫
        Spec.map (CommRingCat.ofHom (ProjectivePresentations.degreeZeroConstants R n).toRingHom)) = _
    rw [degreeZeroConstants_eq_algebraMap]
    exact MapOverBase.projectiveMap_over_base _ _ (Polynomial.Reindex.polynomialReindexGraded R e.symm)
      (Polynomial.Reindex.polynomialReindexGraded_irrelevant R e.symm) (by
        intro r
        exact MvPolynomial.rename_C e.symm r))

/-- A reindexing identifies relative projective spaces over the same arbitrary base. -/
def relativeProjectiveSpaceReindexIso (S : Scheme.{u}) (e : σ ≃ Fin (n + 1)) :
    Over.mk (HilbertScheme.Presentations.Relative.GrassmannianProjectivity.PolynomialProjective.relativeProjectiveSpaceProjection σ S) ≅ ProjectivePresentations.projectiveSpaceOver S n :=
  (Over.pullback S.toSpecΓ).mapIso (affineProjectiveSpaceReindexIso Γ(S, ⊤) e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex
