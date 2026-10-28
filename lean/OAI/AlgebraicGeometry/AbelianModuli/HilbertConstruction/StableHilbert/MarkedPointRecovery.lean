import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffinePrescribedPoints

/-! # Marked Point Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.MarkedPointRecovery

noncomputable section

/-! Homogeneous coordinates of an original marked section recover the
prescribed projective point on its stable Hilbert chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem stableHilbertPrescribedPoint_from_homogeneous
    (R : Type u) [CommRing R]
    {C : Type u} [CommRing C] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ) {f : Spec (.of C) ⟶ Spec (.of R)}
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
    (hc : c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H = x)
    (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C n H) {X : Scheme.{u}}
    (e : X ⟶ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient I.ideal)
    (p : X ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n).left)
    (he : (e ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n = p)
    (z : Fin m) (s : Spec (.of C) ⟶ X)
    (hp : (s ≫ e) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C
        (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) x ⟨z⟩)
        (j.coordinate z) (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j (.of C) x ⟨z⟩)) :
    s ≫ p = (PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z).left := by
  subst x
  have hq := AffinePrescribedPoints.stableHilbertPrescribedPoint_affine R i j D H c z
  calc
    s ≫ p = ((s ≫ e) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) ≫
        AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n := by
      exact (congrArg (fun a => s ≫ a) he.symm).trans
        ((Category.assoc s (e ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal)
          (AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n)).symm.trans
          (congrArg (fun a => a ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n)
            (Category.assoc s e (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal)).symm))
    _ = _ := (congrArg
      (fun a => a ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n) hp).trans hq.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.MarkedPointRecovery
