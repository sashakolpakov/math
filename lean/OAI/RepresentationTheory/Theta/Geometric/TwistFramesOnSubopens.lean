import OAI.RepresentationTheory.Theta.Geometric.OpenFrameScalars

/-! # Twist Frames On Subopens -/

namespace OAI.RepresentationTheory.Theta.Geometric.TwistFramesOnSubopens

noncomputable section

/-! The actual pulled-back twist frames on arbitrary subopens. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {n : ℕ} (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (d : ℤ)

def algebraicPullbackTwistFrameOn (i : Fin (n + 1)) (W : X.Opens)
    (hW : W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i) :
    ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n d)).sheaf).restrict W.ι ≅
      AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj W.toScheme :=
  AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hW (Intrinsic.TwistFrames.algebraicPullbackTwistFrame f d i)

theorem algebraicPullbackTwistFrameOn_restrict (i : Fin (n + 1)) {U V : X.Opens}
    (hVU : V ≤ U) (hU : U ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i) :
    AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU (algebraicPullbackTwistFrameOn f d i U hU) =
      algebraicPullbackTwistFrameOn f d i V (hVU.trans hU) :=
  AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp hU hVU _

theorem algebraicPullbackTwistFrameOn_transition (i k : Fin (n + 1)) (W : X.Opens)
    (hW : W ≤ f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) :
    (algebraicPullbackTwistFrameOn f d i W
      (hW.trans (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k)))).hom =
    (algebraicPullbackTwistFrameOn f d k W
      (hW.trans (f.preimage_mono (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i k)))).hom ≫
      AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        (W.topIso.inv (PowerGaugeCover.restrictRegularUnit hW (PowerGauge.projectivePullbackTransitionUnit f i k ^ d) : Γ(X, W))) := by
  have h := OpenFrameScalars.restrictOpenFrame_scalar
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (AlgebraicQuotient.algebraicTwistBundle n d)).sheaf hW _ _
    ((PowerGauge.projectivePullbackTransitionUnit f i k ^ d :
      Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)ˣ) :
      Γ(X, f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k))
    (Intrinsic.TwistFrames.algebraicPullbackTwistFrame_transition f d i k)
  rw [AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp, AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric.TwistFramesOnSubopens
