import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.DetectedPolynomial
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized

/-! # Specialized Polynomial Predicate -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecializedPolynomialPredicate.Intrinsic

noncomputable section

/-! Keep the comparison model explicit when transporting the exact
specialized ordinary polynomial. -/

open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

variable {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {jq : K →+* ℚ_[q]} (X : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H] (ρ : X.HeckeRealization H) (h : Fin 3 → H)

def SpecializedOrdinaryPolynomial : Prop :=
  HeckeCycles.Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
    (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) X.specialFiber.scheme)
    (fun i => HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction X ρ (h i))

theorem specializedOrdinaryPolynomial_intro
    (hp : HeckeCycles.Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Polynomial q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) X.specialFiber.scheme)
      (fun i => HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction X ρ (h i))) :
    SpecializedOrdinaryPolynomial X ρ h := hp

theorem specializedOrdinaryPolynomial_value (hp : SpecializedOrdinaryPolynomial X ρ h) :
    HeckeCycles.Ordinary.Polynomial.CM.heckePolynomialValue q
      (FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) X.specialFiber.scheme)
      (fun i => HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction X ρ (h i)) = 0 := hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SpecializedPolynomialPredicate.Intrinsic
