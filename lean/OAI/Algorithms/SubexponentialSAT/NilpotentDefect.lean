import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.WeightedSupport
import OAI.Algorithms.SubexponentialSAT.LiftRing

namespace OAI.Algorithms

/-!
# Divisibility of the marked defect

After the input coordinates have been substituted, the coefficient of U in
each incidence argument is divisible by p. Polynomial operations preserve
the stronger invariant that the coefficient of U^j is divisible by p^j.
This proves the high-U vanishing needed by canonical truncation.
-/

namespace SubexponentialSAT.NilpotentDefect

noncomputable section

open scoped BigOperators

section General

variable {A : Type*} [CommSemiring A]

/-- The coefficient of the j-th power carries at least j copies of p. -/
def PowerDivisible (p : A) (P : Polynomial A) : Prop :=
  ∀ j, p ^ j ∣ P.coeff j

theorem powerDivisible_zero (p : A) :
    PowerDivisible p (0 : Polynomial A) := by
  intro j
  simp

theorem powerDivisible_add {p : A} {P Q : Polynomial A}
    (hP : PowerDivisible p P) (hQ : PowerDivisible p Q) :
    PowerDivisible p (P + Q) := by
  intro j
  rw [Polynomial.coeff_add]
  exact dvd_add (hP j) (hQ j)

theorem powerDivisible_mul {p : A} {P Q : Polynomial A}
    (hP : PowerDivisible p P) (hQ : PowerDivisible p Q) :
    PowerDivisible p (P * Q) := by
  classical
  intro j
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro ab hab
  have hj : ab.1 + ab.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  rw [← hj, pow_add]
  exact mul_dvd_mul (hP ab.1) (hQ ab.2)

theorem powerDivisible_monomial (p a : A) (n : ℕ) (ha : p ^ n ∣ a) :
    PowerDivisible p (Polynomial.monomial n a) := by
  intro j
  by_cases h : n = j
  · subst j
    simpa using ha
  · simp [Polynomial.coeff_monomial, h]

theorem powerDivisible_C (p a : A) :
    PowerDivisible p (Polynomial.C a) := by
  simpa using powerDivisible_monomial p a 0 (by simp)

theorem powerDivisible_one (p : A) :
    PowerDivisible p (1 : Polynomial A) := by
  simpa using powerDivisible_C p 1

theorem powerDivisible_sum {α : Type*} (p : A) (s : Finset α)
    (f : α → Polynomial A) (hf : ∀ a ∈ s, PowerDivisible p (f a)) :
    PowerDivisible p (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using powerDivisible_zero p
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact powerDivisible_add (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem powerDivisible_prod {α : Type*} (p : A) (s : Finset α)
    (f : α → Polynomial A) (hf : ∀ a ∈ s, PowerDivisible p (f a)) :
    PowerDivisible p (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using powerDivisible_one p
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact powerDivisible_mul (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem powerDivisible_eval₂ {B σ : Type*} [CommSemiring B]
    (p : A) (f : B →+* Polynomial A) (C : σ → Polynomial A)
    (F : MvPolynomial σ B)
    (hf : ∀ b, PowerDivisible p (f b))
    (hC : ∀ i, PowerDivisible p (C i)) :
    PowerDivisible p (MvPolynomial.eval₂ f C F) := by
  induction F using MvPolynomial.induction_on with
  | C b => simpa using hf b
  | add F G hF hG =>
    simpa only [MvPolynomial.eval₂_add] using powerDivisible_add hF hG
  | mul_X F i hF =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using
      powerDivisible_mul hF (hC i)

/-- Nilpotence kills every complete high-degree coefficient, after evaluation. -/
theorem high_coeff_eq_zero {p : A} {P : Polynomial A} {μ : ℕ}
    (hP : PowerDivisible p P) (hnil : p ^ μ = 0) (j : ℕ) (hj : μ ≤ j) :
    P.coeff j = 0 := by
  apply eq_zero_of_zero_dvd
  simpa only [pow_eq_zero_of_le hj hnil] using hP j

end General

section Inputs

variable {R ι : Type*} [CommRing R]

/-- Identical to Truncation.substX; kept here to avoid a module import cycle. -/
def evalInputs (x : ι → R) :
    SubexponentialSAT.WeightedSupport.Poly ι R →+* Polynomial (Polynomial R) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.eval x))

theorem evalInputs_scalar (x : ι → R) (c : R) :
    evalInputs x (SubexponentialSAT.WeightedSupport.scalarHom c) =
      Polynomial.C (Polynomial.C c) := by
  simp [evalInputs, SubexponentialSAT.WeightedSupport.scalarHom]

/-- Substitution retains U as a formal variable. The entire U coefficient
is the lifted-value defect, without any termwise divisibility assertion. -/
theorem evalInputs_incidenceArgument (x : ι → R) (β : R)
    (L : MvPolynomial ι R) (s : Finset ℕ) (rows : ℕ → MvPolynomial ι R) :
    evalInputs x (SubexponentialSAT.WeightedSupport.incidenceArgument β L s rows) =
      Polynomial.C (Polynomial.C β) +
        Polynomial.monomial 1 (Polynomial.C (MvPolynomial.eval x L - β)) +
        ∑ r ∈ s, Polynomial.C (Polynomial.monomial r (MvPolynomial.eval x (rows r))) := by
  classical
  simp [evalInputs, SubexponentialSAT.WeightedSupport.incidenceArgument,
    SubexponentialSAT.WeightedSupport.markedArgument, SubexponentialSAT.WeightedSupport.scalarHom,
    Polynomial.map_sum]

/-- The actual incidence polynomial has the divisibility invariant as soon
as its evaluated defect is divisible by p. No hypothesis on individual
symbolic monomials is used. -/
theorem powerDivisible_incidenceArgument (x : ι → R) (p β : R)
    (L : MvPolynomial ι R) (s : Finset ℕ) (rows : ℕ → MvPolynomial ι R)
    (hdefect : p ∣ MvPolynomial.eval x L - β) :
    PowerDivisible (Polynomial.C p)
      (evalInputs x (SubexponentialSAT.WeightedSupport.incidenceArgument β L s rows)) := by
  rw [evalInputs_incidenceArgument]
  apply powerDivisible_add
  · apply powerDivisible_add
    · exact powerDivisible_C _ _
    · apply powerDivisible_monomial
      simpa only [pow_one] using map_dvd Polynomial.C hdefect
  · apply powerDivisible_sum
    intro r hr
    exact powerDivisible_C _ _

theorem powerDivisible_evalInputs_factor {σ : Type*}
    (x : ι → R) (p : R) (F : MvPolynomial σ R)
    (C : σ → SubexponentialSAT.WeightedSupport.Poly ι R)
    (hC : ∀ i, PowerDivisible (Polynomial.C p) (evalInputs x (C i))) :
    PowerDivisible (Polynomial.C p)
      (evalInputs x
        (MvPolynomial.eval₂ (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι)) C F)) := by
  rw [MvPolynomial.eval₂_comp_left (evalInputs x)
    (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι)) C F]
  apply powerDivisible_eval₂
  · intro c
    change PowerDivisible (Polynomial.C p)
      (evalInputs x (SubexponentialSAT.WeightedSupport.scalarHom c))
    rw [evalInputs_scalar]
    exact powerDivisible_C _ _
  · exact hC

/-- Divisibility for the full product of actual table polynomials at the
actual marked incidence arguments. -/
theorem powerDivisible_factor_product {α : Type*} {σ : α → Type*}
    (x : ι → R) (p : R) (s : Finset α)
    (F : ∀ e, MvPolynomial (σ e) R)
    (β : ∀ e, σ e → R) (L : ∀ e, σ e → MvPolynomial ι R)
    (zs : ∀ e, σ e → Finset ℕ)
    (rows : ∀ e, σ e → ℕ → MvPolynomial ι R)
    (hdefect : ∀ e ∈ s, ∀ i, p ∣ MvPolynomial.eval x (L e i) - β e i) :
    PowerDivisible (Polynomial.C p)
      (evalInputs x
        (∏ e ∈ s, MvPolynomial.eval₂ (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι))
          (fun i => SubexponentialSAT.WeightedSupport.incidenceArgument
            (β e i) (L e i) (zs e i) (rows e i)) (F e))) := by
  rw [map_prod]
  apply powerDivisible_prod
  intro e he
  apply powerDivisible_evalInputs_factor
  intro i
  exact powerDivisible_incidenceArgument x p (β e i) (L e i) (zs e i)
    (rows e i) (hdefect e he i)

/-- This is precisely the high-U premise of Truncation.canonical_substitution,
proved for the complete incidence-factor construction. -/
theorem highU_factor_product {α : Type*} {σ : α → Type*}
    (x : ι → R) (p : R) (μ : ℕ) (hnil : p ^ μ = 0) (s : Finset α)
    (F : ∀ e, MvPolynomial (σ e) R)
    (β : ∀ e, σ e → R) (L : ∀ e, σ e → MvPolynomial ι R)
    (zs : ∀ e, σ e → Finset ℕ)
    (rows : ∀ e, σ e → ℕ → MvPolynomial ι R)
    (hdefect : ∀ e ∈ s, ∀ i, p ∣ MvPolynomial.eval x (L e i) - β e i)
    (j : ℕ) (hj : μ ≤ j) :
    (evalInputs x
      (∏ e ∈ s, MvPolynomial.eval₂ (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι))
        (fun i => SubexponentialSAT.WeightedSupport.incidenceArgument
          (β e i) (L e i) (zs e i) (rows e i)) (F e))).coeff j = 0 := by
  apply high_coeff_eq_zero
    (powerDivisible_factor_product x p s F β L zs rows hdefect) _ j hj
  simp only [← map_pow, hnil, map_zero]

end Inputs

section Units

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A total inverse selector; its laws require a proved unit hypothesis.
This mathematical selector does not claim a computational cost. -/
noncomputable def unitInverse (a : R) : R := by
  classical
  exact if h : IsUnit a then (h.unit⁻¹ : Rˣ) else 0

theorem mul_unitInverse {a : R} (ha : IsUnit a) :
    a * unitInverse a = 1 := by
  classical
  simpa only [unitInverse, dite_eq_left ha] using ha.mul_val_inv

theorem unitInverse_mul {a : R} (ha : IsUnit a) :
    unitInverse a * a = 1 := by
  rw [mul_comm]
  exact mul_unitInverse ha

/-- Explicit finite geometric correction of an approximate inverse b. -/
def geometricInverse (a b : R) (μ : ℕ) : R :=
  b * ∑ j ∈ Finset.range μ, (1 - a * b) ^ j

theorem mul_geometricInverse (a b : R) (μ : ℕ)
    (hnil : (1 - a * b) ^ μ = 0) :
    a * geometricInverse a b μ = 1 := by
  unfold geometricInverse
  rw [← mul_assoc]
  have h := mul_neg_geom_sum (1 - a * b) μ
  simpa only [sub_sub_cancel, hnil, sub_zero] using h

theorem geometricInverse_mul (a b : R) (μ : ℕ)
    (hnil : (1 - a * b) ^ μ = 0) :
    geometricInverse a b μ * a = 1 := by
  rw [mul_comm]
  exact mul_geometricInverse a b μ hnil

/-- The residue inverse is lifted by any specified section, then corrected
by a finite geometric sum in the original ring. -/
def residueInverse {K : Type*} [Field K] (ρ : R →+* K)
    (lift : K → R) (μ : ℕ) (a : R) : R :=
  geometricInverse a (lift ((ρ a)⁻¹)) μ

theorem mul_residueInverse {K : Type*} [Field K] (ρ : R →+* K)
    (lift : K → R) (hsection : ∀ z, ρ (lift z) = z)
    (p : R) (μ : ℕ) (hnil : p ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → p ∣ x)
    (a : R) (ha : ρ a ≠ 0) :
    a * residueInverse ρ lift μ a = 1 := by
  apply mul_geometricInverse
  have hz : ρ (1 - a * lift ((ρ a)⁻¹)) = 0 := by
    simp only [map_sub, map_one, map_mul, hsection, mul_inv_cancel₀ ha, sub_self]
  obtain ⟨d, hd⟩ := hker _ hz
  rw [hd, mul_pow, hnil, zero_mul]

/-- A unit lifts along a surjection whose kernel consists of nilpotents.
The proof corrects any lifted inverse by the finite geometric-series unit. -/
theorem isUnit_of_nilpotent_kernel (ρ : R →+* S)
    (hρ : Function.Surjective ρ)
    (hker : ∀ x, ρ x = 0 → IsNilpotent x)
    {a : R} (ha : IsUnit (ρ a)) : IsUnit a := by
  obtain ⟨b, hb⟩ := ha.exists_right_inv
  obtain ⟨c, hc⟩ := hρ b
  have hz : ρ (a * c - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hc, hb, sub_self]
  have hu := (hker (a * c - 1) hz).isUnit_add_one
  have hu' : IsUnit (a * c) := by
    simpa only [sub_add_cancel] using hu
  exact isUnit_of_mul_isUnit_left hu'

theorem isUnit_of_principal_nilpotent_kernel (ρ : R →+* S)
    (hρ : Function.Surjective ρ)
    (p : R) (μ : ℕ) (hnil : p ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → p ∣ x)
    {a : R} (ha : IsUnit (ρ a)) : IsUnit a := by
  apply isUnit_of_nilpotent_kernel ρ hρ _ ha
  intro x hx
  obtain ⟨d, hd⟩ := hker x hx
  refine ⟨μ, ?_⟩
  rw [hd, mul_pow, hnil, zero_mul]

theorem isUnit_of_residue_ne_zero {K : Type*} [Field K]
    (ρ : R →+* K) (hρ : Function.Surjective ρ)
    (p : R) (μ : ℕ) (hnil : p ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → p ∣ x)
    {a : R} (ha : ρ a ≠ 0) : IsUnit a :=
  isUnit_of_principal_nilpotent_kernel ρ hρ p μ hnil hker ha.isUnit

end Units

section ConcreteRing

open SubexponentialSAT.LiftRing

/-- Concrete prime-power extension: every element with nonzero residue is
a unit. The residue field is the quotient by the reduced irreducible F. -/
theorem isUnit_of_lambda_residue_ne_zero
    (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    {F : Polynomial (Base p μ)} (hF : F.Monic)
    (hirr : Irreducible (F.map (baseReduction p μ hμ)))
    {a : Lambda p μ F} (ha : residue p μ hμ F a ≠ 0) :
    IsUnit a := by
  let _ : Field (Extension (F.map (baseReduction p μ hμ))) :=
    extensionField (K := ZMod p) hirr
  apply isUnit_of_residue_ne_zero (residue p μ hμ F)
    (residue_surjective p μ hμ F) (p : Lambda p μ F) μ
    (prime_power_zero p μ F) _ ha
  intro x hx
  exact (residue_eq_zero_iff p μ hμ hF x).mp hx

end ConcreteRing

end

end SubexponentialSAT.NilpotentDefect

end OAI.Algorithms
