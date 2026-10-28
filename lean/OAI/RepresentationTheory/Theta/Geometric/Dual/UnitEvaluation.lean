import OAI.RepresentationTheory.Theta.Geometric.Dual.OpenSectionValues
import OAI.RepresentationTheory.Theta.Geometric.PowerGaugeCover

/-! # Unit Evaluation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.UnitEvaluation

noncomputable section

/-! Inverses of actual regular units are evaluated using the genuine
inverse in the dual-number ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem dualUnit_inv_value (u : (DualNumber ℂ)ˣ) :
    ((u⁻¹ : (DualNumber ℂ)ˣ) : DualNumber ℂ) = (u : DualNumber ℂ)⁻¹ := by
  apply u.isUnit.mul_left_cancel
  have hn : (u : DualNumber ℂ).fst ≠ 0 :=
    isUnit_iff_ne_zero.mp (TrivSqZeroExt.isUnit_iff_isUnit_fst.mp u.isUnit)
  exact u.val_inv.trans (TrivSqZeroExt.mul_inv_cancel hn).symm

theorem dualRingHom_unit_inv {R : Type*} [CommRing R]
    (f : R →+* DualNumber ℂ) (u : Rˣ) :
    f ((u⁻¹ : Rˣ) : R) = (f (u : R))⁻¹ := by
  change ((Units.map f.toMonoidHom (u⁻¹) : (DualNumber ℂ)ˣ) : DualNumber ℂ) = _
  rw [map_inv]
  exact dualUnit_inv_value _

theorem restrictRegularUnit_dualValue {X : Scheme} {U W : X.Opens}
    (h : W ≤ U) (u : Γ(X, U)ˣ) (p : Spec (.of (DualNumber ℂ)) ⟶ X)
    (hp : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤ p ⁻¹ᵁ W) :
    OpenSectionValues.dualSectionValue p W hp (PowerGaugeCover.restrictRegularUnit h u : Γ(X, W)) =
      OpenSectionValues.dualSectionValue p U (hp.trans (p.preimage_mono h)) (u : Γ(X, U)) :=
  OpenSectionValues.dualSectionValue_restrict p U W h hp u

theorem projectivePullbackTransitionUnit_dualValue {X : Scheme} {n : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (p : Spec (.of (DualNumber ℂ)) ⟶ X)
    (i j : Fin (n + 1))
    (hp : (⊤ : (Spec (.of (DualNumber ℂ))).Opens) ≤
      p ⁻¹ᵁ (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i j)) :
    OpenSectionValues.dualSectionValue p (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i j) hp
      (PowerGauge.projectivePullbackTransitionUnit f i j : Γ(X, _)) =
    OpenSectionValues.dualSectionValue (p ≫ f) (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i j) hp
      (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i j : Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n, _)) := by
  have H := OpenSectionValues.dualSectionValue_pullback p f (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i j)
    (f ⁻¹ᵁ AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i j) le_rfl hp
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := ℂ) i j : Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n, _))
  rw [Scheme.Hom.appLE_eq_app] at H
  exact H

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.UnitEvaluation
