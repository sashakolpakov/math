import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AutomorphismTwists
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialTwistComparison

/-! # Automorphism Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AutomorphismPolynomial

noncomputable section

/-! The actual homogeneous Hilbert-polynomial predicate of a closed
projective subscheme is invariant under every base-preserving projective automorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

theorem projectiveAutomorphism_hilbertPolynomial_iff
    (e : Proj (Hilbert.Polynomial.GradedHilbert.grading K n) ≅ Proj (Hilbert.Polynomial.GradedHilbert.grading K n)) (he : e.hom ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ = SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)
    {X : Scheme.{u}} (j : X ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K n)) [IsClosedImmersion j] (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (j ≫ e.hom).ker).toIdeal P ↔
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf j.ker).toIdeal P := by
  apply Hilbert.PolynomialTwistComparison.hilbertPolynomial_iff_of_twist_pullback_isos (j ≫ e.hom) j (j ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)
    (by rw [Category.assoc, he]) rfl 0 _ P
  intro m
  let a := (AutomorphismTwists.projectiveAutomorphism_preserves_native_twists K e he m).some
  exact ⟨((Scheme.Modules.pullbackComp j e.hom).app
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) (0 : Fin (n + 1)) m)).symm ≪≫
      (Scheme.Modules.pullback j).mapIso a⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AutomorphismPolynomial
