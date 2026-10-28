import OAI.ArithmeticGeometry.Models.SpreadingOut.BoundedPolynomial
import OAI.ArithmeticGeometry.Models.SpreadingOut.AlgebraicSpecialization

/-! # Factorization Algebra -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FactorizationAlgebra.Construction.PolynomialFactorization

noncomputable section

/-! Finite-type algebras parameterizing bounded nonconstant factorizations. -/

open _root_.MvPolynomial
open scoped BigOperators

universe u

abbrev Variables (n d : ℕ) := (Fin 2 × BoundedPolynomial.Construction.PolynomialBox n d) ⊕ Fin 2
abbrev Coefficients (R : Type u) [CommRing R] (n d : ℕ) := MvPolynomial (Variables n d) R

def universalFactor (R : Type u) [CommRing R] (n d : ℕ) (i : Fin 2) :
    MvPolynomial (Fin n) (Coefficients R n d) :=
  BoundedPolynomial.Construction.boundedPolynomial (fun v ↦ X (Sum.inl (i, v)))

def discrepancy {R : Type u} [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R) (d : ℕ) :
    MvPolynomial (Fin n) (Coefficients R n d) :=
  MvPolynomial.map (algebraMap R (Coefficients R n d)) p -
    universalFactor R n d 0 * universalFactor R n d 1

def relations {R : Type u} [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R) (d : ℕ)
    (w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d) : Set (Coefficients R n d) :=
  Set.range (fun m ↦ (discrepancy p d).coeff m) ∪
    Set.range (fun i : Fin 2 ↦ X (Sum.inr i) * X (Sum.inl (i, w i)) - 1)

def ideal {R : Type u} [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R) (d : ℕ)
    (w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d) : Ideal (Coefficients R n d) :=
  Ideal.span (relations p d w)

abbrev ParameterAlgebra {R : Type u} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d) :=
  Coefficients R n d ⧸ ideal p d w

def evalCoefficients {R k : Type u} [CommRing R] [CommRing k] [Algebra R k]
    {n d : ℕ} {p : MvPolynomial (Fin n) R} {w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d}
    (φ : ParameterAlgebra p d w →ₐ[R] k) : Coefficients R n d →ₐ[R] k :=
  φ.comp (Ideal.Quotient.mkₐ R (ideal p d w))

def evalFactor {R k : Type u} [CommRing R] [CommRing k] [Algebra R k]
    {n d : ℕ} {p : MvPolynomial (Fin n) R} {w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d}
    (φ : ParameterAlgebra p d w →ₐ[R] k) (i : Fin 2) : MvPolynomial (Fin n) k :=
  MvPolynomial.map (evalCoefficients φ).toRingHom (universalFactor R n d i)

theorem eval_relation_zero {R k : Type u} [CommRing R] [CommRing k] [Algebra R k]
    {n d : ℕ} {p : MvPolynomial (Fin n) R} {w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d}
    (φ : ParameterAlgebra p d w →ₐ[R] k) {r : Coefficients R n d} (hr : r ∈ relations p d w) :
    evalCoefficients φ r = 0 := by
  change φ (Ideal.Quotient.mk (ideal p d w) r) = 0
  have hz : Ideal.Quotient.mk (ideal p d w) r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)
  rw [hz, map_zero]

theorem evalFactor_product {R k : Type u} [CommRing R] [CommRing k] [Algebra R k]
    {n d : ℕ} {p : MvPolynomial (Fin n) R} {w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d}
    (φ : ParameterAlgebra p d w →ₐ[R] k) :
    MvPolynomial.map (algebraMap R k) p = evalFactor φ 0 * evalFactor φ 1 := by
  have h : MvPolynomial.map (evalCoefficients φ).toRingHom (discrepancy p d) = 0 := by
    ext m
    rw [coeff_map, AddMonoidAlgebra.coeff_zero]
    exact eval_relation_zero φ (Or.inl ⟨m, rfl⟩)
  have hp : MvPolynomial.map (evalCoefficients φ).toRingHom
      (MvPolynomial.map (algebraMap R (Coefficients R n d)) p) =
      MvPolynomial.map (algebraMap R k) p := by
    rw [map_map]
    exact congrArg (fun f : R →+* k ↦ MvPolynomial.map f p) (evalCoefficients φ).comp_algebraMap
  apply sub_eq_zero.mp
  simpa only [discrepancy, map_sub, map_mul, hp, evalFactor] using h

theorem evalFactor_nonconstant_coeff {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {n d : ℕ} {p : MvPolynomial (Fin n) R} {w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d}
    (φ : ParameterAlgebra p d w →ₐ[R] k) (i : Fin 2) :
    (evalFactor φ i).coeff (BoundedPolynomial.Construction.polynomialBoxExponent (w i)) ≠ 0 := by
  have he := eval_relation_zero φ (Or.inr ⟨i, rfl⟩)
  have hm : evalCoefficients φ (X (Sum.inr i)) * evalCoefficients φ (X (Sum.inl (i, w i))) = 1 := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_mul, map_one] using he
  rw [evalFactor, coeff_map, universalFactor, BoundedPolynomial.Construction.boundedPolynomial_coeff]
  exact (mul_ne_zero_iff.mp (hm.trans_ne one_ne_zero)).2

theorem no_points_of_irreducible {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {n d : ℕ} {p : MvPolynomial (Fin n) R} {w : Fin 2 → BoundedPolynomial.Construction.PolynomialBox n d}
    (hw : ∀ i, BoundedPolynomial.Construction.polynomialBoxExponent (w i) ≠ 0)
    (hp : Irreducible (MvPolynomial.map (algebraMap R k) p)) :
    IsEmpty (ParameterAlgebra p d w →ₐ[R] k) := by
  refine ⟨fun φ ↦ ?_⟩
  have hu (i : Fin 2) : ¬ IsUnit (evalFactor φ i) :=
    BoundedPolynomial.Construction.polynomial_not_isUnit_of_nonconstant_coefficient (hw i) (evalFactor_nonconstant_coeff φ i)
  exact (hp.isUnit_or_isUnit (evalFactor_product φ)).elim (hu 0) (hu 1)

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FactorizationAlgebra.Construction.PolynomialFactorization
