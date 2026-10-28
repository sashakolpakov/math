import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ReindexOpens
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Dehomogenization

/-! # Reindex Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ReindexSections

noncomputable section

/-! Reindexing projective variables preserves their actual regular
coordinate-ratio sections on the corresponding standard opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective

universe u v

private theorem projectiveMap_variable_section
    (R : CommRingCat.{max u v}) {σ : Type u} {τ : Type v}
    (f : Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading τ R →+*ᵍ Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R)
    (hf : HomogeneousIdeal.irrelevant (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) ≤
      (HomogeneousIdeal.irrelevant (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading τ R)).map f)
    (i j : τ) (t z : MvPolynomial σ R) (ht : t = f (X i)) (hz : z = f (X j))
    (htm : t ∈ Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R 1) (hzm : z ∈ Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R (1 • (1 : ℕ)))
    (h : Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) t ≤
      Proj.map f hf ⁻¹ᵁ Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading τ R) (X i)) :
    (Proj.map f hf).appLE (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading τ R) (X i))
      (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) t) h
      (Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading τ R) (X i) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) =
    Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) t
      (HomogeneousLocalization.Away.mk (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) htm 1 z hzm) := by
  subst t
  subst z
  have he := Proj.awayToSection_comp_appLE f hf (isHomogeneous_X R i)
  have hv := congrArg (fun k : CommRingCat.of (HomogeneousLocalization.Away (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading τ R) (X i)) ⟶
    Γ(Proj (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R), Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (f (X i))) =>
      k (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) he
  change (Proj.map f hf).appLE (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading τ R) (X i))
    (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (f (X i))) h
    (Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading τ R) (X i) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) =
      Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (f (X i))
        (HomogeneousLocalization.Away.map f (X i) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) at hv
  rw [Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_X] at hv
  erw [Polynomial.Dehomogenization.PolynomialProjective.coordinateFraction, HomogeneousLocalization.Away.map_mk] at hv
  simpa only [Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_X, Polynomial.Dehomogenization.PolynomialProjective.coordinateFraction] using hv

variable (R : CommRingCat.{u}) {σ : Type u} {n : ℕ} (e : σ ≃ Fin (n + 1))

def e33CoordinateRatioSection (N : ℕ) (i j : Fin (N + 1)) :
    Γ(Proj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R N), Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R N) (X i)) :=
  Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R N) (X i) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))

theorem e33ProjectiveReindex_section (i j : Fin (n + 1))
    (h : Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X (e.symm i)) ≤
      (AbelianModuli.HilbertConstruction.Projective.SpaceReindex.affineProjectiveSpaceReindexIso R e).hom.left ⁻¹ᵁ
        Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X i)) :
    (AbelianModuli.HilbertConstruction.Projective.SpaceReindex.affineProjectiveSpaceReindexIso R e).hom.left.appLE
      (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X i))
      (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X (e.symm i))) h
      (Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X i) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize i (X j))) =
    Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X (e.symm i))
      (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (e.symm i) (X (e.symm j))) := by
  conv_rhs => rw [Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_X]; unfold Polynomial.Dehomogenization.PolynomialProjective.coordinateFraction
  let f := AbelianModuli.HilbertConstruction.Polynomial.Reindex.polynomialReindexGraded R e.symm
  have hf : HomogeneousIdeal.irrelevant (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) ≤
      (HomogeneousIdeal.irrelevant (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (Fin (n + 1)) R)).map f :=
    AbelianModuli.HilbertConstruction.Polynomial.Reindex.polynomialReindexGraded_irrelevant R e.symm
  have hv := projectiveMap_variable_section R f hf i j (X (e.symm i)) (X (e.symm j))
    (rename_X e.symm i).symm (rename_X e.symm j).symm
    (isHomogeneous_X R (e.symm i)) (by simpa only [one_smul] using! isHomogeneous_X R (e.symm j)) h
  exact hv

theorem e33ProjectiveReindex_section_apply (p q : σ)
    (h : Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X p) ≤
      (AbelianModuli.HilbertConstruction.Projective.SpaceReindex.affineProjectiveSpaceReindexIso R e).hom.left ⁻¹ᵁ
        Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X (e p))) :
    (AbelianModuli.HilbertConstruction.Projective.SpaceReindex.affineProjectiveSpaceReindexIso R e).hom.left.appLE
      (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X (e p)))
      (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X p)) h
      (Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X (e p)) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize (e p) (X (e q)))) =
    Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X p) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p (X q)) := by
  conv_rhs => rw [Polynomial.Dehomogenization.PolynomialProjective.dehomogenize_X]; unfold Polynomial.Dehomogenization.PolynomialProjective.coordinateFraction
  let f := AbelianModuli.HilbertConstruction.Polynomial.Reindex.polynomialReindexGraded R e.symm
  have hf : HomogeneousIdeal.irrelevant (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading σ R) ≤
      (HomogeneousIdeal.irrelevant (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (Fin (n + 1)) R)).map f :=
    AbelianModuli.HilbertConstruction.Polynomial.Reindex.polynomialReindexGraded_irrelevant R e.symm
  have hv := projectiveMap_variable_section R f hf (e p) (e q) (X p) (X q)
    (by simpa only [Equiv.symm_apply_apply] using! (rename_X e.symm (e p)).symm)
    (by simpa only [Equiv.symm_apply_apply] using! (rename_X e.symm (e q)).symm)
    (isHomogeneous_X R p) (by simpa only [one_smul] using! isHomogeneous_X R q) h
  exact hv

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ReindexSections
