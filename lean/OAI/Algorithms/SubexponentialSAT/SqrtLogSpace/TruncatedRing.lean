import OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrderArray
import Mathlib.Algebra.Ring.InjSurj

/-!
# Dense lifting and Taylor coefficients

`Truncated R n` stores exactly `n` coefficients. Its multiplication is the
existing total-order convolution, and its ring laws follow from the surjective
coefficient projection from `R[X]`. Nesting the construction stores the shared
lifting marker outside the Taylor variable. The final marker readout is additive.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrder

/-- A dense canonical representative modulo the indicated power of the variable. -/
@[ext] structure Truncated (R : Type*) (n : ℕ) where
  coeff : Fin n → R

namespace Truncated

variable {R : Type*} {n : ℕ}

instance [Zero R] : Zero (Truncated R n) := ⟨⟨fun _ => 0⟩⟩
instance [Zero R] [One R] : One (Truncated R n) :=
  ⟨⟨fun j => if j.val = 0 then 1 else 0⟩⟩
instance [Add R] : Add (Truncated R n) := ⟨fun a b => ⟨fun j => a.coeff j + b.coeff j⟩⟩
instance [SMul ℕ R] : SMul ℕ (Truncated R n) := ⟨fun k a => ⟨fun j => k • a.coeff j⟩⟩
instance [Zero R] [NatCast R] : NatCast (Truncated R n) :=
  ⟨fun k => ⟨fun j => if j.val = 0 then k else 0⟩⟩
instance [CommSemiring R] : Mul (Truncated R n) :=
  ⟨fun a b => ⟨mulArray a.coeff b.coeff⟩⟩
instance [CommSemiring R] : Pow (Truncated R n) ℕ := ⟨fun a k => npowRec k a⟩

@[simp] theorem coeff_zero [Zero R] (j : Fin n) : (0 : Truncated R n).coeff j = 0 := rfl
@[simp] theorem coeff_one [Zero R] [One R] (j : Fin n) :
    (1 : Truncated R n).coeff j = if j.val = 0 then 1 else 0 := rfl
@[simp] theorem coeff_add [Add R] (a b : Truncated R n) (j : Fin n) :
    (a + b).coeff j = a.coeff j + b.coeff j := rfl
@[simp] theorem coeff_nsmul [SMul ℕ R] (k : ℕ) (a : Truncated R n) (j : Fin n) :
    (k • a).coeff j = k • a.coeff j := rfl
@[simp] theorem coeff_natCast [Zero R] [NatCast R] (k : ℕ) (j : Fin n) :
    (k : Truncated R n).coeff j = if j.val = 0 then (k : R) else 0 := rfl

section Semiring

variable [CommSemiring R]

/-- Explicit bounded convolution, with out-of-range reads equal to zero. -/
theorem coeff_mul (a b : Truncated R n) (j : Fin n) :
    (a * b).coeff j = ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal j.val,
      arrayCoeff a.coeff uv.1 * arrayCoeff b.coeff uv.2 := rfl

noncomputable section

/-- The coefficient projection. This is a semantic map, not the native evaluator. -/
def ofPolynomial (n : ℕ) (P : Polynomial R) : Truncated R n := ⟨toArray n P⟩

/-- The canonical polynomial represented by the stored array. -/
def polynomial (a : Truncated R n) : Polynomial R := asPolynomial a.coeff

@[simp] theorem coeff_ofPolynomial (P : Polynomial R) (j : Fin n) :
    (ofPolynomial n P).coeff j = P.coeff j.val := rfl

@[simp] theorem ofPolynomial_polynomial (a : Truncated R n) :
    ofPolynomial n a.polynomial = a := by
  ext j
  simp [ofPolynomial, polynomial]

theorem ofPolynomial_surjective : Function.Surjective (ofPolynomial (R := R) n) :=
  fun a => ⟨a.polynomial, ofPolynomial_polynomial a⟩

@[simp] theorem ofPolynomial_zero : ofPolynomial n (0 : Polynomial R) = 0 := by
  ext j
  simp

@[simp] theorem ofPolynomial_one : ofPolynomial n (1 : Polynomial R) = 1 := by
  ext j
  simp [Polynomial.coeff_one]

@[simp] theorem ofPolynomial_add (P Q : Polynomial R) :
    ofPolynomial n (P + Q) = ofPolynomial n P + ofPolynomial n Q := by
  ext j
  simp

@[simp] theorem ofPolynomial_mul (P Q : Polynomial R) :
    ofPolynomial n (P * Q) = ofPolynomial n P * ofPolynomial n Q := by
  ext j
  rw [coeff_ofPolynomial, coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro uv huv
  have huv' := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have hu : uv.1 < n := by omega
  have hv : uv.2 < n := by omega
  simp [arrayCoeff, hu, hv]

@[simp] theorem ofPolynomial_nsmul (k : ℕ) (P : Polynomial R) :
    ofPolynomial n (k • P) = k • ofPolynomial n P := by
  ext j
  change (k • P).coeff j.val = k • P.coeff j.val
  exact Polynomial.coeff_smul k P j.val

@[simp] theorem ofPolynomial_pow (P : Polynomial R) (k : ℕ) :
    ofPolynomial n (P ^ k) = ofPolynomial n P ^ k := by
  induction k with
  | zero => exact ofPolynomial_one
  | succ k ih =>
      change ofPolynomial n (P ^ (k + 1)) = npowRec k (ofPolynomial n P) * ofPolynomial n P
      rw [pow_succ, ofPolynomial_mul, ih]
      rfl

@[simp] theorem ofPolynomial_natCast (k : ℕ) :
    ofPolynomial n (k : Polynomial R) = k := by
  ext j
  simp [Polynomial.coeff_natCast_ite]

instance : CommSemiring (Truncated R n) :=
  ofPolynomial_surjective.commSemiring (ofPolynomial n)
    ofPolynomial_zero ofPolynomial_one ofPolynomial_add ofPolynomial_mul
    ofPolynomial_nsmul ofPolynomial_pow ofPolynomial_natCast

/-- Each stored coordinate is additive, but generally not multiplicative. -/
def coeffHom (j : Fin n) : Truncated R n →+ R where
  toFun a := a.coeff j
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coeff_sum {ι : Type*} (s : Finset ι) (a : ι → Truncated R n) (j : Fin n) :
    (∑ i ∈ s, a i).coeff j = ∑ i ∈ s, (a i).coeff j :=
  map_sum (coeffHom j) a s

/-- The quotient-ring projection is multiplicative; the marker readout is not. -/
def ofPolynomialHom (n : ℕ) : Polynomial R →+* Truncated R n where
  toFun := ofPolynomial n
  map_zero' := ofPolynomial_zero
  map_one' := ofPolynomial_one
  map_add' := ofPolynomial_add
  map_mul' := ofPolynomial_mul

/-- Add the coefficients of the chosen representative, after multiplication. -/
def readout : Truncated R n →+ R where
  toFun a := ∑ j : Fin n, a.coeff j
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

theorem readout_eq_eval (a : Truncated R n) : readout a = a.polynomial.eval 1 :=
  sumArray_eq_eval a.coeff

theorem readout_mul (a b : Truncated R n) :
    readout (a * b) = (OAI.Algorithms.SubexponentialSAT.Truncation.trunc n (a.polynomial * b.polynomial)).eval 1 := by
  rw [readout_eq_eval]
  exact congrArg (fun P : Polynomial R => P.eval 1) (asPolynomial_mulArray a.coeff b.coeff)

end
end Semiring

section Ring

variable [CommRing R]

instance : Neg (Truncated R n) := ⟨fun a => ⟨fun j => -a.coeff j⟩⟩
instance : Sub (Truncated R n) := ⟨fun a b => ⟨fun j => a.coeff j - b.coeff j⟩⟩
instance : SMul ℤ (Truncated R n) := ⟨fun k a => ⟨fun j => k • a.coeff j⟩⟩
instance : IntCast (Truncated R n) := ⟨fun k => ⟨fun j => if j.val = 0 then k else 0⟩⟩

noncomputable section

@[simp] theorem ofPolynomial_neg (P : Polynomial R) :
    ofPolynomial n (-P) = -ofPolynomial n P := by
  ext j
  change (-P).coeff j.val = -P.coeff j.val
  simp

@[simp] theorem ofPolynomial_sub (P Q : Polynomial R) :
    ofPolynomial n (P - Q) = ofPolynomial n P - ofPolynomial n Q := by
  ext j
  change (P - Q).coeff j.val = P.coeff j.val - Q.coeff j.val
  simp

@[simp] theorem ofPolynomial_zsmul (k : ℤ) (P : Polynomial R) :
    ofPolynomial n (k • P) = k • ofPolynomial n P := by
  ext j
  change (k • P).coeff j.val = k • P.coeff j.val
  simp

@[simp] theorem ofPolynomial_intCast (k : ℤ) :
    ofPolynomial n (k : Polynomial R) = k := by
  ext j
  change (k : Polynomial R).coeff j.val = if j.val = 0 then (k : R) else 0
  rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C]

instance : CommRing (Truncated R n) :=
  ofPolynomial_surjective.commRing (ofPolynomial n)
    ofPolynomial_zero ofPolynomial_one ofPolynomial_add ofPolynomial_mul
    ofPolynomial_neg ofPolynomial_sub ofPolynomial_nsmul ofPolynomial_zsmul
    ofPolynomial_pow ofPolynomial_natCast ofPolynomial_intCast

@[simp] theorem coeff_neg (a : Truncated R n) (j : Fin n) :
    (-a).coeff j = -a.coeff j := rfl

@[simp] theorem coeff_sub (a b : Truncated R n) (j : Fin n) :
    (a - b).coeff j = a.coeff j - b.coeff j := rfl

@[simp] theorem coeff_zsmul (k : ℤ) (a : Truncated R n) (j : Fin n) :
    (k • a).coeff j = k • a.coeff j := rfl

end
end Ring
end Truncated

/-- `t * J` scalar slots: shared lifting marker outside, Taylor variable inside. -/
abbrev Dense (R : Type*) (t J : ℕ) := Truncated (Truncated R J) t

namespace Dense

variable {R : Type*} [CommSemiring R] {t J : ℕ}

noncomputable section

/-- First project Taylor coefficients, then truncate the shared marker. -/
def ofPolynomial (t J : ℕ) : Polynomial (Polynomial R) →+* Dense R t J :=
  (Truncated.ofPolynomialHom t).comp
    (Polynomial.mapRingHom (Truncated.ofPolynomialHom J))

@[simp] theorem coeff_ofPolynomial (P : Polynomial (Polynomial R)) (u : Fin t) (z : Fin J) :
    ((ofPolynomial t J P).coeff u).coeff z = (P.coeff u.val).coeff z.val := by
  simp [ofPolynomial, Truncated.ofPolynomialHom]

/-- Final additive shared-marker readout; a Taylor array remains. -/
def readout : Dense R t J →+ Truncated R J := Truncated.readout

@[simp] theorem coeff_readout (a : Dense R t J) (z : Fin J) :
    (readout a).coeff z = ∑ u : Fin t, (a.coeff u).coeff z := by
  exact Truncated.coeff_sum Finset.univ a.coeff z

theorem readout_ofPolynomial (P : Polynomial (Polynomial R)) :
    readout (ofPolynomial t J P) =
      Truncated.ofPolynomial J ((OAI.Algorithms.SubexponentialSAT.Truncation.trunc t P).eval 1) := by
  ext z
  rw [coeff_readout, Truncated.coeff_ofPolynomial, eval_one_trunc]
  simp only [coeff_ofPolynomial, Polynomial.finsetSum_coeff]
  exact Fin.sum_univ_eq_sum_range (fun u => (P.coeff u).coeff z.val) t

end
end Dense
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
