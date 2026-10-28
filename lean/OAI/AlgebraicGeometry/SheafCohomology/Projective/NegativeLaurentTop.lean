import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentHomology
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechTopSupport

/-! # Negative Laurent Top -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop

noncomputable section

open _root_.MvPolynomial

/-! Top positive cohomology is the space of full-negative Laurent coefficients. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedCechTopSupport
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateFullNegativeCyclesEquivCochain (d : ℤ) (n : ℕ) :
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCycles.{u, u} (R := R) (σ := σ) d n ≃ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)]
        LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u, u} (R := R) (σ := σ) d n where
  toFun := Subtype.val
  invFun s := ⟨s, by
    change LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential (R := R) d n s = 0
    rw [NegativeLaurentDifferential.MvPolynomial.coordinateHomogeneousLaurentFullNegativeDifferential_eq_zero, LinearMap.zero_apply]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinateFullNegativeCochainTopEquiv (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 1) :
    LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u, u} (R := R) (σ := σ) d n ≃ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)]
        ({e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
          e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} → Γ(Spec (CommRingCat.of R), ⊤)) :=
  LinearEquiv.piCongrRight fun e =>
    (LinearEquiv.ofEq
      (OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (CommRingCat.of R), ⊤) e.val.liftedNegativeSupport n)
      (OrderedCechSupportContraction.OrderedCechSupportCochain Γ(Spec (CommRingCat.of R), ⊤) (Set.univ : Set (ULift.{u} σ)) n)
      (by rw [e.property])).trans
        (OrderedCechTopSupport.orderedCechFullSupportTopEquiv Γ(Spec (CommRingCat.of R), ⊤) n (by simpa using hn))

def coordinateHomogeneousLaurentTopHomologyEquivCoefficients
    (j : σ) (d : ℤ) (n : ℕ) (hn : Fintype.card σ = n + 2) :
    (TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology (n + 1) ≃ₗ[
      Γ(Spec (CommRingCat.of R), ⊤)]
        ({e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
          e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} → Γ(Spec (CommRingCat.of R), ⊤)) :=
  (NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles (R := R) j d n).trans
    ((coordinateFullNegativeCyclesEquivCochain (R := R) d (n + 1)).trans
      (coordinateFullNegativeCochainTopEquiv (R := R) d (n + 1) hn))

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop
