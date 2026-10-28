import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentExceptionalWeights

/-! # Negative Laurent Differential -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentDifferential

noncomputable section

open _root_.MvPolynomial

/-! The full-negative Laurent part has zero differential and splits off at the cochain level. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechSupport
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHomogeneousLaurentFullNegativeDifferential_eq_zero (d : ℤ) (n : ℕ) :
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential.{u, u} (R := R) (σ := σ) d n = 0 := by
  apply LinearMap.ext
  intro s
  funext e
  rw [LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential_apply]
  have hzero : OrderedCechSupportContraction.orderedCechSupportDifferential Γ(Spec (CommRingCat.of R), ⊤)
      e.val.liftedNegativeSupport n = 0 := by
    rw [e.property, OrderedCechSupport.orderedCechSupportDifferential_univ]
  simpa only [LinearMap.zero_apply, Pi.zero_apply] using (LinearMap.congr_fun hzero (s e))

theorem coordinateHomogeneousLaurentFullNegativeProjection_boundary (d : ℤ) (n : ℕ)
    (s : LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n) :
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection (R := R) d (n + 1)
      ((LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechDifferential (R := R) (σ := σ) d n).hom s) = 0 := by
  rw [← LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection_differential,
    coordinateHomogeneousLaurentFullNegativeDifferential_eq_zero, LinearMap.zero_apply]

variable [Fintype σ]

theorem coordinateHomogeneousLaurentFullNegativeProjection_assembly (d : ℤ) (n : ℕ)
    (s : LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain (R := R) (σ := σ) d n) :
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection (R := R) d n
      (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly (R := R) (σ := σ) d n s) = s := by
  classical
  let : Fintype {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    (LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ (σ := σ) d).fintype
  funext e
  rw [LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeProjection_apply,
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeAssembly_apply, map_sum]
  rw [Finset.sum_eq_single e]
  · exact TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_inclusion (R := R) d e.val n (s e)
  · intro f _ hfe
    exact TwistCechWeightComponents.MvPolynomial.coordinateHomogeneousLaurentWeightComponent_inclusion_ne (R := R) d f.val e.val
      (fun h => hfe (Subtype.ext h.symm)) n (s f)
  · intro h
    exact (h (Finset.mem_univ e)).elim

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentDifferential
