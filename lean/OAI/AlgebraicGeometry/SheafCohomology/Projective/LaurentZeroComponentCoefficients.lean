import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.EmptySupportCycleEvaluation

/-! # Laurent Zero Component Coefficients -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroComponentCoefficients

noncomputable section

/-! The Laurent coefficients of zero cycles are global nonnegative polynomial coefficients. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.EmptySupportCycleEvaluation
universe u
namespace MvPolynomial
open _root_.MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]

theorem laurentZeroComponent_coeff_nonnegative (n : ℕ) (j : σ)
    (z : LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) (n : ℤ))
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0)
    (e : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ)) :
    (LaurentCoordinates.MvPolynomial.homogeneousLaurentZeroComponent (n : ℤ) z a).coeff
        (PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed (fun k => (a.val k).down) n e) =
      LaurentZeroCoefficients.MvPolynomial.laurentZeroCoefficients (R := R) (n : ℤ) j z e := by
  let c := LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight (R := R) (n : ℤ) e.val z
  have hp := TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_apply_of_allowed
    (R := R) (n : ℤ) e.val a
    (PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed (fun k => (a.val k).down) n e).property z.val
  have hc := EmptySupportCycleEvaluation.orderedEmptySupportCyclesEquiv_eq_component Γ(Spec (CommRingCat.of R), ⊤)
    e.val.liftedNegativeSupport e.emptySupport (ULift.up j) c a
  exact hp.symm.trans hc.symm

theorem laurentZeroComponent_coeff_negative (n : ℕ) (j : σ)
    (z : LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) (n : ℤ))
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0)
    (e : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ (n : ℤ) //
      e.IsAllowedOn (fun k => (a.val k).down)})
    (he : ¬ ∀ i, 0 ≤ e.val.val i) :
    (LaurentCoordinates.MvPolynomial.homogeneousLaurentZeroComponent (n : ℤ) z a).coeff e = 0 := by
  have hneg : ∃ i, e.val.val i < 0 := by
    push Not at he
    exact he
  obtain ⟨i, hi⟩ := hneg
  have hN : (e.val.liftedNegativeSupport : Set (ULift.{u} σ)) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp ⟨ULift.up i, hi⟩
  have hz := LaurentZeroCycleWeights.MvPolynomial.laurentZeroCycleWeight_eq_zero_of_nonempty (R := R) (n : ℤ)
    (Int.natCast_nonneg n) j e.val hN z
  have hv := congrArg (fun c => c.val.val a) hz
  have hp := TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_apply_of_allowed
    (R := R) (n : ℤ) e.val a e.property z.val
  exact hp.symm.trans hv

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroComponentCoefficients
