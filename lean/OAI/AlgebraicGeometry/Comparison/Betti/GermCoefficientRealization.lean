import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms

/-! # Germ Coefficient Realization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GermCoefficientRealization.AnalyticLocal

noncomputable section

/-! Coefficient extraction commutes with realization of germ polynomials.
In particular, realization retains every coefficient. -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs

def germMapAddHom {X R S : Type*} [AddMonoid R] [AddMonoid S]
    (l : Filter X) (f : R →+ S) : Germ l R →+ Germ l S where
  toFun := Germ.map f
  map_zero' := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun _ => map_zero f)
  map_add' a b := by
    induction a, b using Germ.inductionOn₂ with
    | h u v =>
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (fun y => map_add f (u y) (v y))

def germPolynomialCoeff {E : Type*} (l : Filter E) (k : ℕ) : Germ l ℂ[X] →+ Germ l ℂ :=
  germMapAddHom l
    { toFun := fun P => P.coeff k
      map_zero' := coeff_zero k
      map_add' := fun P Q => coeff_add P Q k }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem polynomialRealization_coeff (x : E) (Q : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]) (j : ℕ) :
    germPolynomialCoeff (𝓝 x) j (ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialRealization x Q) = (Q.coeff j).val := by
  induction Q using Polynomial.induction_on' with
  | add Q₁ Q₂ ih₁ ih₂ =>
    rw [map_add, map_add, ih₁, ih₂, coeff_add]
    rfl
  | monomial k a =>
    obtain ⟨f, hfa, U, hU, hx, hf⟩ := a.property
    have ha : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x f hU hx hf = a := Subtype.ext hfa
    rw [← ha, ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.realize_monomial_ofFunction]
    change ((fun y => (monomial k (f y)).coeff j) : Germ (𝓝 x) ℂ) = _
    by_cases hkj : k = j
    · simp only [coeff_monomial, hkj, ite_true]
      rfl
    · simp only [coeff_monomial, ite_eq_right hkj]
      rfl

theorem polynomialRealization_injective (x : E) : Function.Injective (ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialRealization x) := by
  intro P Q h
  ext k
  simpa only [polynomialRealization_coeff] using congrArg (germPolynomialCoeff (𝓝 x) k) h

theorem polynomialRealization_representative_coeff (x : E) (Q : (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X])
    (P : E → ℂ[X]) (hP : ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs.polynomialRealization x Q = (P : Germ (𝓝 x) ℂ[X])) (k : ℕ) :
    ((fun y => (P y).coeff k) : Germ (𝓝 x) ℂ) = (Q.coeff k).val := by
  rw [← polynomialRealization_coeff x Q k, hP]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.GermCoefficientRealization.AnalyticLocal
