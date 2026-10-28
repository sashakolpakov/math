import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Polynomial Germs -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs

noncomputable section

/-!
# Realizing polynomials of holomorphic germs

Polynomial identities between coefficient germs become identities of
polynomial-valued function germs. Finite polynomial degree bounds then turn
these identities into actual equations on a common neighborhood.
-/

open Set Filter _root_.Polynomial
open scoped _root_.Topology BigOperators

def mapGermRingHom {X R S : Type*} [Semiring R] [Semiring S]
    (l : Filter X) (φ : R →+* S) : Germ l R →+* Germ l S where
  toFun := Germ.map φ
  map_zero' := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun _ => map_zero φ)
  map_one' := by
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun _ => map_one φ)
  map_add' := by
    intro a b
    induction a, b using Germ.inductionOn₂ with
    | h f g =>
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (fun x => map_add φ (f x) (g x))
  map_mul' := by
    intro a b
    induction a, b using Germ.inductionOn₂ with
    | h f g =>
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (fun x => map_mul φ (f x) (g x))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def polynomialRealization (x : E) : (HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X] →+* Germ (𝓝 x) ℂ[X] :=
  Polynomial.eval₂RingHom
    ((mapGermRingHom (𝓝 x) (C : ℂ →+* ℂ[X])).comp (HolomorphicGerms.Constructions.Germs.holomorphicGerms x).subtype)
    (Germ.const X)

theorem realize_C_of_representative (x : E) (a : HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) (f : E → ℂ)
    (hf : (f : Germ (𝓝 x) ℂ) = a.val) :
    polynomialRealization x (C a) = ((fun y => C (f y)) : Germ (𝓝 x) ℂ[X]) := by
  change Polynomial.eval₂ _ _ (C a) = _
  rw [eval₂_C]
  change Germ.map (C : ℂ → ℂ[X]) a.val = _
  rw [← hf, Germ.map_coe]
  rfl

theorem realize_monomial_ofFunction (x : E) (f : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) (k : ℕ) :
    polynomialRealization x (monomial k (HolomorphicGerms.Constructions.Germs.ofFunction x f hU hx hf)) =
      ((fun y => monomial k (f y)) : Germ (𝓝 x) ℂ[X]) := by
  change Polynomial.eval₂ _ _ (monomial k (HolomorphicGerms.Constructions.Germs.ofFunction x f hU hx hf)) = _
  rw [eval₂_monomial]
  change (Germ.map (C : ℂ → ℂ[X]) (f : Germ (𝓝 x) ℂ)) *
    ((fun _ : E => (X : ℂ[X])) : Germ (𝓝 x) ℂ[X]) ^ k = _
  simp only [Germ.map_coe, ← Germ.coe_pow, ← Germ.coe_mul]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun _ => C_mul_X_pow_eq_monomial)

/-- A polynomial in holomorphic germs has a polynomial-valued representative
with a fixed degree bound and holomorphic coefficients on one neighborhood. -/
theorem exists_polynomial_representative (x : E) (Q : (HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X]) :
    ∃ (d : ℕ) (P : E → ℂ[X]) (U : Set E), IsOpen U ∧ x ∈ U ∧
      (∀ y, (P y).natDegree ≤ d) ∧
      (∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U) ∧
      polynomialRealization x Q = (P : Germ (𝓝 x) ℂ[X]) := by
  induction Q using Polynomial.induction_on' with
  | add Q₁ Q₂ ih₁ ih₂ =>
    obtain ⟨d₁, P₁, U₁, hU₁, hx₁, hd₁, hp₁, hq₁⟩ := ih₁
    obtain ⟨d₂, P₂, U₂, hU₂, hx₂, hd₂, hp₂, hq₂⟩ := ih₂
    refine ⟨max d₁ d₂, (fun y => P₁ y + P₂ y), U₁ ∩ U₂, hU₁.inter hU₂,
      ⟨hx₁, hx₂⟩, fun y => (natDegree_add_le (P₁ y) (P₂ y)).trans (max_le_max (hd₁ y) (hd₂ y)), ?_, ?_⟩
    · intro k
      simp only [coeff_add]
      exact (hp₁ k |>.mono inter_subset_left).add (hp₂ k |>.mono inter_subset_right)
    · rw [map_add, hq₁, hq₂]
      exact (Germ.coe_add P₁ P₂).symm
  | monomial k a =>
    obtain ⟨f, hfa, U, hU, hx, hf⟩ := a.property
    have ha : HolomorphicGerms.Constructions.Germs.ofFunction x f hU hx hf = a := Subtype.ext hfa
    refine ⟨k, (fun y => monomial k (f y)), U, hU, hx,
      fun y => natDegree_monomial_le (f y), ?_, ?_⟩
    · intro j
      simp only [coeff_monomial]
      split_ifs
      · exact hf
      · exact differentiableOn_const _
    · rw [← ha]
      exact realize_monomial_ofFunction x f hU hx hf k

def polynomialOfFamily (x : E) (P : E → ℂ[X]) (d : ℕ) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U)
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U) : (HolomorphicGerms.Constructions.Germs.HolomorphicGerm x)[X] :=
  ∑ k ∈ Finset.range (d + 1), monomial k (HolomorphicGerms.Constructions.Germs.ofFunction x (fun y => (P y).coeff k) hU hx (hcoeff k))

theorem realize_polynomialOfFamily (x : E) (P : E → ℂ[X]) (d : ℕ) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U)
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree ≤ d) :
    polynomialRealization x (polynomialOfFamily x P d hU hx hcoeff) = (P : Germ (𝓝 x) ℂ[X]) := by
  simp only [polynomialOfFamily, map_sum, realize_monomial_ofFunction]
  rw [← Germ.coe_sum]
  apply Germ.coe_eq.mpr
  filter_upwards [hU.mem_nhds hx] with y hy
  simp only [Finset.sum_apply]
  change (∑ k ∈ Finset.range (d + 1), monomial k ((P y).coeff k)) = P y
  apply Polynomial.funext
  intro z
  simp only [eval_finsetSum, eval_monomial]
  exact (eval_eq_sum_range' (lt_of_le_of_lt (hdegree y hy) (Nat.lt_succ_self d)) z).symm

theorem polynomialOfFamily_ne_zero (x : E) (P : E → ℂ[X]) (d : ℕ) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U)
    (hcoeff : ∀ k : ℕ, DifferentiableOn ℂ (fun y => (P y).coeff k) U)
    (hdegree : ∀ y ∈ U, (P y).natDegree ≤ d) (hP : P x ≠ 0) :
    polynomialOfFamily x P d hU hx hcoeff ≠ 0 := by
  intro hz
  have hreal := realize_polynomialOfFamily x P d hU hx hcoeff hdegree
  rw [hz, map_zero] at hreal
  have hzero : ∀ᶠ y in 𝓝 x, P y = 0 := Germ.coe_eq.mp hreal.symm
  exact hP hzero.self_of_nhds

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGerms.Constructions.Germs
