import OAI.AlgebraicGeometry.Divisors.LineBundles.ReesCoefficients
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Homogeneous Rees -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.HomogeneousRees.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual Rees polynomial recording each homogeneous degree -/

variable {A ι : Type} [CommRing A]

def polynomialHomogeneousMap : MvPolynomial ι A →+* Polynomial (MvPolynomial ι A) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.monomial 1 (MvPolynomial.X i))

theorem polynomial_product_monomial {R κ : Type} [CommRing R] (s : Finset κ)
    (d : κ → ℕ) (c : κ → R) :
    (∏ i ∈ s, Polynomial.monomial (d i) (c i)) =
      Polynomial.monomial (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, Polynomial.monomial_mul_monomial]

theorem polynomialHomogeneousMap_monomial (d : ι →₀ ℕ) (a : A) :
    polynomialHomogeneousMap (MvPolynomial.monomial d a) =
      Polynomial.monomial d.degree (MvPolynomial.monomial d a) := by
  classical
  change MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.monomial 1 (MvPolynomial.X i)) (MvPolynomial.monomial d a) = _
  rw [MvPolynomial.eval₂_monomial]
  simp only [Polynomial.monomial_pow, one_mul, Finsupp.prod,
    polynomial_product_monomial, RingHom.comp_apply, Polynomial.C_mul_monomial]
  rw [MvPolynomial.monomial_eq]
  rfl

theorem polynomialHomogeneousMap_coeff (p : MvPolynomial ι A) (n : ℕ) :
    (polynomialHomogeneousMap p).coeff n = MvPolynomial.homogeneousComponent n p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [polynomialHomogeneousMap_monomial, Polynomial.coeff_monomial,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial a rfl)]
    simp only [eq_comm]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]

def polynomialHomogeneousRees : MvPolynomial ι A →+* reesAlgebra (MvPolynomial.idealOfVars ι A) where
  toFun p := ⟨polynomialHomogeneousMap p, fun n => by
    rw [polynomialHomogeneousMap_coeff, MvPolynomial.mem_pow_idealOfVars_iff']
    intro d hd
    rw [MvPolynomial.coeff_homogeneousComponent, ite_eq_right (Nat.ne_of_lt hd)]⟩
  map_zero' := Subtype.ext (map_zero polynomialHomogeneousMap)
  map_one' := Subtype.ext (map_one polynomialHomogeneousMap)
  map_add' p q := Subtype.ext (map_add polynomialHomogeneousMap p q)
  map_mul' p q := Subtype.ext (map_mul polynomialHomogeneousMap p q)

theorem polynomialHomogeneousRees_coeff (p : MvPolynomial ι A) (n : ℕ) :
    (polynomialHomogeneousRees p).val.coeff n = MvPolynomial.homogeneousComponent n p :=
  polynomialHomogeneousMap_coeff p n

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.HomogeneousRees.BundleCycles
