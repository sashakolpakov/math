import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Evaluation

/-! # Fractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Fractions

noncomputable section

/-! Evaluation of homogeneous-localization functions when their denominator evaluates to a unit. -/

universe u

variable {R B : Type u} [CommRing R] [CommRing B] {n : ℕ}

/-- Evaluate a homogeneous fraction whenever its homogeneous denominator becomes invertible. -/
def homogeneousFractionEvaluation (c : R →+* B) (v : Fin (n + 1) → B)
    (f : Projective.ProjectivePresentations.coordinateRing R n) (hf : IsUnit (MvPolynomial.eval₂Hom c v f)) :
    HomogeneousLocalization.Away (Projective.ProjectivePresentations.coordinateGrading R n) f →+* B :=
  (Localization.awayLift (MvPolynomial.eval₂Hom c v) f hf).comp
    (algebraMap (HomogeneousLocalization.Away (Projective.ProjectivePresentations.coordinateGrading R n) f) (Localization.Away f))

/-- The evaluation is numerator times the chosen inverse denominator to the appropriate power. -/
theorem homogeneousFractionEvaluation_mk (c : R →+* B) (v : Fin (n + 1) → B)
    (f : Projective.ProjectivePresentations.coordinateRing R n) (hf : IsUnit (MvPolynomial.eval₂Hom c v f))
    (e : ℕ) (hfe : f ∈ Projective.ProjectivePresentations.coordinateGrading R n e) (d : ℕ)
    (p : Projective.ProjectivePresentations.coordinateRing R n) (hp : p ∈ Projective.ProjectivePresentations.coordinateGrading R n (d • e))
    (w : B) (hw : MvPolynomial.eval₂Hom c v f * w = 1) :
    homogeneousFractionEvaluation c v f hf
      (HomogeneousLocalization.Away.mk (Projective.ProjectivePresentations.coordinateGrading R n) hfe d p hp) =
        MvPolynomial.eval₂Hom c v p * w ^ d := by
  change (Localization.awayLift (MvPolynomial.eval₂Hom c v) f (isUnit_iff_exists_inv.mpr ⟨w, hw⟩))
    (Localization.mk p ⟨f ^ d, d, rfl⟩) = _
  exact Localization.awayLift_mk (MvPolynomial.eval₂Hom c v) f p w hw d

/-- Normalized chart evaluation is the special case with denominator value one. -/
theorem projectiveChartEvaluation_eq_fraction (c : R →+* B) (v : Fin (n + 1) → B)
    (i : Fin (n + 1)) (hi : v i = 1)
    (hf : IsUnit (MvPolynomial.eval₂Hom c v (MvPolynomial.X i))) :
    ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi = homogeneousFractionEvaluation c v (MvPolynomial.X i) hf := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Fractions
