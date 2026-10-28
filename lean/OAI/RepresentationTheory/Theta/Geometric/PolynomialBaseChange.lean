import OAI.RepresentationTheory.Theta.Geometric.Projective.ChartSchemes

/-! # Polynomial Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.PolynomialBaseChange.RelativeProjective

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R S : Type} [CommRing R] [CommRing S]

theorem polynomial_isPullback (f : R →+* S) (n : ℕ) (i : Fin (n + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.map f :
      Projective.Charts.RelativeProjective.projectiveChartPolynomial R n i →+* Projective.Charts.RelativeProjective.projectiveChartPolynomial S n i)))
      (Projective.ChartSchemes.RelativeProjective.projectiveChartPolynomialToBase S n i) (Projective.ChartSchemes.RelativeProjective.projectiveChartPolynomialToBase R n i)
      (Spec.map (CommRingCat.ofHom f)) := by
  let J := {j : Fin (n + 1) // j ≠ i}
  apply (AffineSpace.isPullback_map (n := J) (Spec.map (CommRingCat.ofHom f))).of_iso
    (AffineSpace.SpecIso J (.of S)) (AffineSpace.SpecIso J (.of R))
    (Iso.refl _) (Iso.refl _)
  · simp [AffineSpace.map_SpecMap]
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [← Iso.inv_comp_eq]
    exact AffineSpace.SpecIso_inv_over (n := J) (.of S)
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [← Iso.inv_comp_eq]
    exact AffineSpace.SpecIso_inv_over (n := J) (.of R)
  · simp

end

end OAI.RepresentationTheory.Theta.Geometric.PolynomialBaseChange.RelativeProjective
