import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.GradedRenaming
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap

/-! # Projective Renaming -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveRenaming.PolynomialProjective

noncomputable section

/-! Bijections of homogeneous coordinate variables induce actual projective
scheme isomorphisms compatible with the coefficient-ring structure map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomogeneousLocalization

universe u
variable {R σ : Type u} [CommRing R] {d : ℕ}

def polynomialProjectiveCoordinateIso (e : σ ≃ Fin (d + 1)) :
    Proj (Dehomogenization.PolynomialProjective.polynomialGrading σ R) ≅ Proj (Dehomogenization.PolynomialProjective.polynomialGrading (Fin (d + 1)) R) where
  hom := Proj.map (GradedRenaming.PolynomialProjective.gradedRename e.symm) (GradedRenaming.PolynomialProjective.irrelevant_gradedRename_le_map e.symm)
  inv := Proj.map (GradedRenaming.PolynomialProjective.gradedRename e) (GradedRenaming.PolynomialProjective.irrelevant_gradedRename_le_map e)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have h : (GradedRenaming.PolynomialProjective.gradedRename (R := R) e.symm).comp (GradedRenaming.PolynomialProjective.gradedRename e) =
        GradedRingHom.id (Dehomogenization.PolynomialProjective.polynomialGrading σ R) := GradedRenaming.PolynomialProjective.gradedRename_inverse e.symm
    simpa only [h] using (Proj.map_id (𝒜 := Dehomogenization.PolynomialProjective.polynomialGrading σ R))
  inv_hom_id := by
    rw [← Proj.map_comp]
    simpa only [GradedRenaming.PolynomialProjective.gradedRename_inverse e] using
      (Proj.map_id (𝒜 := Dehomogenization.PolynomialProjective.polynomialGrading (Fin (d + 1)) R))

theorem gradedRename_away_algebraMap (e : σ ≃ Fin (d + 1)) (s : MvPolynomial (Fin (d + 1)) R) (r : R) :
    HomogeneousLocalization.Away.map (GradedRenaming.PolynomialProjective.gradedRename e.symm) s
      (algebraMap R (HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R d) s) r) =
        algebraMap R (HomogeneousLocalization.Away (Dehomogenization.PolynomialProjective.polynomialGrading σ R) (GradedRenaming.PolynomialProjective.gradedRename e.symm s)) r := by
  rw [Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap, Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  apply HomogeneousLocalization.val_injective
  change Localization.mk (MvPolynomial.rename e.symm (C r)) ⟨GradedRenaming.PolynomialProjective.gradedRename e.symm 1, _⟩ =
    Localization.mk (C r) 1
  rw [MvPolynomial.rename_C]
  congr 1
  exact Subtype.ext (map_one (GradedRenaming.PolynomialProjective.gradedRename (R := R) e.symm))

theorem polynomialProjectiveCoordinateIso_over (e : σ ≃ Fin (d + 1)) :
    (polynomialProjectiveCoordinateIso (R := R) e).hom ≫
      Projective.Flatness.GradedHilbert.projectiveStructureMap (Dehomogenization.PolynomialProjective.polynomialGrading (Fin (d + 1)) R) =
        Projective.Flatness.GradedHilbert.projectiveStructureMap (Dehomogenization.PolynomialProjective.polynomialGrading σ R) := by
  let f := GradedRenaming.PolynomialProjective.gradedRename (R := R) e.symm
  have hf := GradedRenaming.PolynomialProjective.irrelevant_gradedRename_le_map (R := R) e.symm
  have hspan : (HomogeneousIdeal.irrelevant (Dehomogenization.PolynomialProjective.polynomialGrading σ R)).toIdeal ≤
      Ideal.span (Set.range (fun i : Fin (d + 1) => f (X i))) := by
    apply (show (HomogeneousIdeal.irrelevant (Dehomogenization.PolynomialProjective.polynomialGrading σ R)).toIdeal ≤
      Ideal.map f (HomogeneousIdeal.irrelevant (Hilbert.Polynomial.GradedHilbert.grading R d)).toIdeal from hf).trans
    have h := Ideal.map_mono (f := f.toRingHom)
      (ProjectiveCoefficientMap.GradedHilbert.polynomial_irrelevant_le_span_variables (R := R) (n := d))
    rw [Ideal.map_span, ← Set.range_comp] at h
    exact h
  let U := Proj.affineOpenCoverOfIrrelevantLESpan (Dehomogenization.PolynomialProjective.polynomialGrading σ R)
    (fun i : Fin (d + 1) => f (X i)) (fun i => f.map_mem (isHomogeneous_X R i))
    (fun _ => Nat.zero_lt_one) hspan
  apply U.openCover.hom_ext
  intro i
  change Fin (d + 1) at i
  have hi : X i ∈ Dehomogenization.PolynomialProjective.polynomialGrading (Fin (d + 1)) R 1 := isHomogeneous_X R i
  change Proj.awayι (Dehomogenization.PolynomialProjective.polynomialGrading σ R) (f (X i)) (f.map_mem hi) Nat.zero_lt_one ≫
    (Proj.map f hf ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Dehomogenization.PolynomialProjective.polynomialGrading (Fin (d + 1)) R)) =
    Proj.awayι (Dehomogenization.PolynomialProjective.polynomialGrading σ R) (f (X i)) (f.map_mem hi) Nat.zero_lt_one ≫
      Projective.Flatness.GradedHilbert.projectiveStructureMap (Dehomogenization.PolynomialProjective.polynomialGrading σ R)
  rw [Proj.awayι_comp_map_assoc f hf Nat.zero_lt_one (X i) hi,
    Projective.Flatness.GradedHilbert.projectiveStructureMap_away (Dehomogenization.PolynomialProjective.polynomialGrading (Fin (d + 1)) R) hi,
    Projective.Flatness.GradedHilbert.projectiveStructureMap_away,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact gradedRename_away_algebraMap e (X i)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveRenaming.PolynomialProjective
