import OAI.RepresentationTheory.Theta.Geometric.Pullback.Algebraic
import OAI.RepresentationTheory.Theta.Geometric.OpenSectionPullback
import OAI.RepresentationTheory.Theta.Geometric.PowerGauge

/-! # Twist Transitions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.TwistTransitions

noncomputable section

/-! Exact native hyperplane frame transitions after pullback to an
algebraic model, with coefficients in its actual regular-section ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {n : ℕ} (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (d : ℤ) (i k : Fin (n + 1))

def pullbackTwistOverlapLeftFrame :
    ((Scheme.Modules.pullback f).obj (AlgebraicQuotient.algebraicTwistBundle n d).sheaf).restrict
      (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).ι ≅
        AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme :=
  Algebraic.pullbackOpenFrame f (AlgebraicQuotient.algebraicTwistBundle n d).sheaf
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := ℂ) i k)
      (Algebraic.algebraicTwistRestrictionFrame n d i))

def pullbackTwistOverlapRightFrame :
    ((Scheme.Modules.pullback f).obj (AlgebraicQuotient.algebraicTwistBundle n d).sheaf).restrict
      (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).ι ≅
        AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme :=
  Algebraic.pullbackOpenFrame f (AlgebraicQuotient.algebraicTwistBundle n d).sheaf
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (AlgebraicGeometry.SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := ℂ) i k)
      (Algebraic.algebraicTwistRestrictionFrame n d k))

omit d in
theorem projectivePullbackTransitionTopUnit :
    Units.map (f ∣_ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).appTop.hom.toMonoidHom
        (AlgebraicGeometry.SheafCohomology.Projective.OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := ℂ) i k) =
      Units.map (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).topIso.inv.hom.toMonoidHom
        (PowerGauge.projectivePullbackTransitionUnit f i k) := by
  apply Units.ext
  exact OpenSectionPullback.morphismRestrict_topSection_apply f (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k)
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i k)

theorem pullbackTwistOverlapFrame_transition :
    (pullbackTwistOverlapLeftFrame f d i k).hom =
      (pullbackTwistOverlapRightFrame f d i k).hom ≫
        AlgebraicGeometry.SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
          ((Units.map (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).topIso.inv.hom.toMonoidHom
            (PowerGauge.projectivePullbackTransitionUnit f i k ^ d) :
              Γ((f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)ˣ) :
              Γ((f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)) := by
  have h := Algebraic.pullbackOpenFrame_scalar f (AlgebraicQuotient.algebraicTwistBundle n d).sheaf
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k) _ _ _
    (Algebraic.algebraicTwistRestrictionFrame_transition n d i k)
  apply h.trans
  congr 2
  change ((Units.map (f ∣_ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).appTop.hom.toMonoidHom
      (AlgebraicGeometry.SheafCohomology.Projective.OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := ℂ) i k ^ d) :
        Γ((f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)ˣ) :
        Γ((f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k).toScheme, ⊤)) = _
  rw [map_zpow, projectivePullbackTransitionTopUnit, ← map_zpow]

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.TwistTransitions
