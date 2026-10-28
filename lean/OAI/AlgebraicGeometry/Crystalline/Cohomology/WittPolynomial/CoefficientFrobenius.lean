import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamSemilinearLeft
import OAI.AlgebraicGeometry.Crystalline.Cohomology.AdicSemilinear
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Semilinear.CompletionMap
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Coefficient Frobenius -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius

noncomputable section

/-!
# Witt-coefficient Frobenius on actual completed polynomial forms

The coefficient automorphism fixes polynomial variables. Its semilinear
action on the original differential-symbol complex remains an
isomorphism after integral p-adic completion.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "φ" => WittVector.frobeniusEquiv p k

local instance forwardScalarInverse : RingHomInvPair (φ).toRingHom (φ).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv φ

local instance backwardScalarInverse : RingHomInvPair (φ).symm.toRingHom (φ).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm φ

def polynomialEquiv : P ≃+* P := MvPolynomial.mapEquiv σ φ

theorem polynomialEquiv_base (w : W) :
    polynomialEquiv p k σ (algebraMap W P w) = algebraMap W P (φ w) := by
  change MvPolynomial.map (φ).toRingHom (MvPolynomial.C w) = MvPolynomial.C (φ w)
  exact MvPolynomial.map_C _ _

def formsEquiv (n : ℕ) : DeRhamPresentationTo.DeRhamPresentation.Form W P n ≃ₛₗ[(φ).toRingHom]
    DeRhamPresentationTo.DeRhamPresentation.Form W P n :=
  DeRhamSemilinearLeft.DeRhamSemilinearEquiv.formsEquiv W W P P φ (polynomialEquiv p k σ) (polynomialEquiv_base p k σ) n

def complexMap : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map (φ).toRingHom
    (DeRhamPresentationTo.DeRhamPresentation.complex W P) (DeRhamPresentationTo.DeRhamPresentation.complex W P) :=
  DeRhamSemilinearA.DeRhamSemilinearMap.complexMap W W P P (φ).toRingHom (polynomialEquiv p k σ).toRingHom
    (polynomialEquiv_base p k σ)

def ideal : Ideal W := Ideal.span {(p : W)}

omit [CharP k p] [PerfectRing k p] in
theorem ideal_map (f : W →+* W) : (ideal p k).map f = ideal p k := by
  rw [ideal, Ideal.map_span, Set.image_singleton, map_natCast]

abbrev completedComplex := Semilinear.CompletionMap.SemilinearCompletionMap.completion (ideal p k) (DeRhamPresentationTo.DeRhamPresentation.complex W P)

def completedMap : NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexMap.Map (φ).toRingHom
    (completedComplex p k σ) (completedComplex p k σ) :=
  Semilinear.CompletionMap.SemilinearCompletionMap.map (φ).toRingHom (ideal p k) (ideal p k)
    (ideal_map p k (φ).toRingHom).le (complexMap p k σ)

def completedFormsEquiv (n : ℕ) :
    AdicCompletion (ideal p k) (DeRhamPresentationTo.DeRhamPresentation.Form W P n) ≃ₛₗ[(φ).toRingHom]
      AdicCompletion (ideal p k) (DeRhamPresentationTo.DeRhamPresentation.Form W P n) :=
  AdicSemilinear.AdicSemilinearEquiv.equiv φ (ideal p k) (ideal p k)
    (ideal_map p k (φ).toRingHom).le (ideal_map p k (φ).symm.toRingHom).le (formsEquiv p k σ n)

def completedLinearMap : completedComplex p k σ ⟶
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (φ).toRingHom (completedComplex p k σ) :=
  NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.linearMap (completedMap p k σ)

instance completed_component_isIso (n : ℕ) : IsIso ((completedLinearMap p k σ).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (completedFormsEquiv p k σ n).bijective

instance completedLinearMap_isIso : IsIso (completedLinearMap p k σ) :=
  HomologicalComplex.Hom.isIso_of_components _

def completedIso : completedComplex p k σ ≅
    NumberTheory.PadicHodge.PeriodInvariants.SemilinearComplexRestriction.restrictedComplex (φ).toRingHom (completedComplex p k σ) :=
  asIso (completedLinearMap p k σ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.CoefficientFrobenius.WittPolynomialCoefficientFrobenius
