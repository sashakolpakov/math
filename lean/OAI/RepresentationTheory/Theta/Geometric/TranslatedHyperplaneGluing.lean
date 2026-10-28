import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing
import OAI.RepresentationTheory.Theta.Geometric.TwistFramesOnSubopens

/-! # Translated Hyperplane Gluing -/

namespace OAI.RepresentationTheory.Theta.Geometric.TranslatedHyperplaneGluing

noncomputable section

/-! Regular comparison gauges give an isomorphism between two actual
hyperplane pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem hyperplane_iso_of_comparison_gauges {X : Scheme} {n : ℕ}
    (f₀ f₁ : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (U : Fin (n + 1) × Fin (n + 1) → X.Opens) (hU : iSup U = ⊤)
    (hU₀ : ∀ p, U p ≤ f₀ ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) p.1)
    (hU₁ : ∀ p, U p ≤ f₁ ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) p.2)
    (r : ∀ p, Γ(X, U p)ˣ)
    (hW₀ : ∀ p q, U p ⊓ U q ≤ f₀ ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) p.1 q.1)
    (hW₁ : ∀ p q, U p ⊓ U q ≤ f₁ ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) p.2 q.2)
    (hr : ∀ p q,
      PowerGaugeCover.restrictRegularUnit (show U p ⊓ U q ≤ U q from inf_le_right) (r q) *
        PowerGaugeCover.restrictRegularUnit (hW₀ p q) (PowerGauge.projectivePullbackTransitionUnit f₀ p.1 q.1) =
      PowerGaugeCover.restrictRegularUnit (show U p ⊓ U q ≤ U p from inf_le_left) (r p) *
        PowerGaugeCover.restrictRegularUnit (hW₁ p q) (PowerGauge.projectivePullbackTransitionUnit f₁ p.2 q.2)) :
    Nonempty ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f₁ (AlgebraicQuotient.algebraicTwistBundle n 1)).sheaf ≅
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f₀ (AlgebraicQuotient.algebraicTwistBundle n 1)).sheaf) := by
  apply IntrinsicFrame.UnitGluing.exists_iso_of_open_framed_units _ _ U hU
    (fun p => TwistFramesOnSubopens.algebraicPullbackTwistFrameOn f₁ 1 p.2 (U p) (hU₁ p))
    (fun p => TwistFramesOnSubopens.algebraicPullbackTwistFrameOn f₀ 1 p.1 (U p) (hU₀ p)) r
    (fun p q => (PowerGaugeCover.restrictRegularUnit (hW₁ p q) (PowerGauge.projectivePullbackTransitionUnit f₁ p.2 q.2) : Γ(X, U p ⊓ U q)))
    (fun p q => (PowerGaugeCover.restrictRegularUnit (hW₀ p q) (PowerGauge.projectivePullbackTransitionUnit f₀ p.1 q.1) : Γ(X, U p ⊓ U q)))
  · intro p q
    rw [TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict, TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict]
    simpa only [zpow_one] using TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_transition f₁ 1 p.2 q.2 (U p ⊓ U q) (hW₁ p q)
  · intro p q
    rw [TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict, TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_restrict]
    simpa only [zpow_one] using TwistFramesOnSubopens.algebraicPullbackTwistFrameOn_transition f₀ 1 p.1 q.1 (U p ⊓ U q) (hW₀ p q)
  · intro p q
    exact (mul_comm _ _).trans (congrArg Units.val (hr p q).symm)

end

end OAI.RepresentationTheory.Theta.Geometric.TranslatedHyperplaneGluing
