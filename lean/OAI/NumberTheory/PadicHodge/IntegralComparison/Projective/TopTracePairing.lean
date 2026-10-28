import OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopCechRightExact
import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityDescent
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Top Trace Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing

noncomputable section

/-! The actual top Čech trace on the canonical projective twist gives a
perfect pairing for every sufficiently negative twist. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistResidueCoordinates
  LaurentResidueNaturality Trace.DualityDescent

universe u

abbrev coefficientRing (R : Type u) [CommRing R] : CommRingCat.{u} :=
  Γ(Spec (CommRingCat.of R), ⊤)

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "C₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing.coefficientRing R

def onePolynomial : homogeneousSubmodule σ C₀ 0 := ⟨1, isHomogeneous_one σ C₀⟩

abbrev topFunctor (n : ℕ) :=
  TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1)

abbrev canonicalTwist (n : ℕ) (hn : Fintype.card σ = n + 2) :=
  AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (n + 2)

omit [LinearOrder σ] in
theorem canonical_degree (n : ℕ) (hn : Fintype.card σ = n + 2) :
    Int.negSucc (n + 1) = -(0 : ℤ) - (Fintype.card σ : ℤ) := by omega

def trace (n : ℕ) (hn : Fintype.card σ = n + 2) :
    (topFunctor (R := R) (σ := σ) n).obj (canonicalTwist (R := R) n hn) ⟶ ModuleCat.of C₀ C₀ :=
  ModuleCat.ofHom
    ((Module.Dual.eval C₀ (homogeneousSubmodule σ C₀ 0) (onePolynomial (R := R) (σ := σ))).comp
      (Intrinsic.TwistResidueCoordinates.cohomologyDual (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (.negSucc (n + 1)) n 0 hn
        (canonical_degree n hn)).toLinearMap)

def negativeDualEquiv (n : ℕ) (hn : Fintype.card σ = n + 2) (A : ℕ) (hA : n + 1 ≤ A) :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (A + 1) ⟶
      canonicalTwist (R := R) n hn) ≃
      Module.Dual C₀ ((topFunctor (R := R) (σ := σ) n).obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (A + 1))) :=
  (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn)
    (A + 1) (n + 2) (Nat.add_le_add_right hA 1)).trans
      (((Module.evalEquiv C₀ (homogeneousSubmodule σ C₀ ((A + 1) - (n + 2)))).trans
        (Intrinsic.TwistResidueCoordinates.cohomologyDual (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (.negSucc A) n
          ((A + 1) - (n + 2)) hn (by omega)).dualMap).toEquiv)

attribute [local irreducible] Intrinsic.TwistResidueCoordinates.cohomologyDual AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials in
theorem negativeDualEquiv_apply (n : ℕ) (hn : Fintype.card σ = n + 2) (A : ℕ) (hA : n + 1 ≤ A)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (A + 1) ⟶
      canonicalTwist (R := R) n hn)
    (x : (topFunctor (R := R) (σ := σ) n).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (A + 1))) :
    negativeDualEquiv (R := R) n hn A hA f x =
      Intrinsic.TwistResidueCoordinates.cohomologyDual (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (.negSucc A) n
        ((A + 1) - (n + 2)) hn (by omega) x
        (AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn)
          (A + 1) (n + 2) (Nat.add_le_add_right hA 1) f) := rfl

attribute [local irreducible] Intrinsic.TwistResidueCoordinates.cohomologyDual AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials in
theorem pairingMap_apply (n : ℕ) (hn : Fintype.card σ = n + 2) (A : ℕ) (hA : n + 1 ≤ A)
    (f : AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (A + 1) ⟶
      canonicalTwist (R := R) n hn)
    (x : (topFunctor (R := R) (σ := σ) n).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (A + 1))) :
    (Trace.DualityDescent.pairingMap (topFunctor (R := R) (σ := σ) n) (trace (R := R) n hn) _ f).hom x =
      negativeDualEquiv (R := R) n hn A hA f x := by
  let m := (A + 1) - (n + 2)
  let P := AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn)
    (A + 1) (n + 2) (Nat.add_le_add_right hA 1) f
  have hP : LaurentResidueNaturality.homogeneousProduct σ C₀ m 0 P (onePolynomial (R := R) (σ := σ)) = P := by
    apply Subtype.ext
    exact mul_one P.val
  have h := NegativeTwistResidueNaturality.cohomologyDual_naturality
    (R := R) n hn A (n + 1) 0 hA (canonical_degree n hn) f
      (onePolynomial (R := R) (σ := σ)) x
  have he := congrArg (fun p : homogeneousSubmodule σ C₀ m =>
    Intrinsic.TwistResidueCoordinates.cohomologyDual (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (.negSucc A) n m hn (by omega) x p) hP
  have hfinal := h.trans he
  rw [negativeDualEquiv_apply]
  exact hfinal

def linearMapHomEquiv {C : Type*} [CommRing C] (V : ModuleCat C) :
    Module.Dual C V ≃ (V ⟶ ModuleCat.of C C) where
  toFun := ModuleCat.ofHom
  invFun f := f.hom
  left_inv _ := rfl
  right_inv _ := rfl

theorem negative_pairing_bijective (n : ℕ) (hn : Fintype.card σ = n + 2) (A : ℕ) (hA : n + 1 ≤ A) :
    Function.Bijective (Trace.DualityDescent.pairingMap (topFunctor (R := R) (σ := σ) n) (trace (R := R) n hn)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (A + 1))) := by
  let e := (negativeDualEquiv (R := R) n hn A hA).trans
    (linearMapHomEquiv ((topFunctor (R := R) (σ := σ) n).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (A + 1))))
  have he : Trace.DualityDescent.pairingMap (topFunctor (R := R) (σ := σ) n) (trace (R := R) n hn)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) (A + 1)) = e := by
    funext f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact pairingMap_apply n hn A hA f x
  rw [he]
  exact e.bijective

theorem negative_pairing_bijective_of_le (n : ℕ) (hn : Fintype.card σ = n + 2)
    (d : ℕ) (hd : n + 2 ≤ d) :
    Function.Bijective (Trace.DualityDescent.pairingMap (topFunctor (R := R) (σ := σ) n) (trace (R := R) n hn)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) d)) := by
  cases d with
  | zero => omega
  | succ A => exact negative_pairing_bijective n hn A (by omega)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing
