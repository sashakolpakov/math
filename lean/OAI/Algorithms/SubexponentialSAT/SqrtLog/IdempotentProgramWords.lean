import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramHalf
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramWords
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramBounds

namespace OAI.Algorithms

/-! Instantiation on fixed-width Boolean words modulo 3^t.  The scalar
callbacks have existing primitive bit-program refinements.  The remaining
native obligation is the runtime-sized array traversal and Newton controller,
not an unprovided algebraic oracle. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

local instance ternaryPrime : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Both the half coefficient and every output coefficient are computed from
word callbacks. No semantic-to-word conversion is used. -/
def wordCoefficientRun (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (Fin (3*t) → RingProgram.ScalarCode 3 t) × ℕ :=
  let ops := RingProgram.scalarProgram 3 t M cache
  let half := halfRun ops t
  let out := coefficientRun ops t half.1
  (out.1, half.2 + out.2 + 1)

def wordOutput (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) : List Bool :=
  RingProgram.flat (wordCoefficientRun t M cache).1

theorem wordOutput_length (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (wordOutput t M cache).length = (3*t)*baseWidth 3 t :=
  RingProgram.flat_length _

theorem wordCoefficientRun_cost (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (wordCoefficientRun t M cache).2 ≤
      (3*t)^3*(36*scalarBudget 3 t+19) + 5*scalarBudget 3 t +
      t*(5*scalarBudget 3 t+8) + 8 +
      Nat.clog 2 t*(7*((3*t+1)^3*(3*scalarBudget 3 t+2))+8) := by
  have hb : ProgramBudget (RingProgram.scalarProgram 3 t M cache) (scalarBudget 3 t) :=
    (RingProgram.scalarRing_budget 3 t M cache).program
  have hh := halfRun_cost _ hb t
  have hc := coefficientRun_cost _ hb t
    (halfRun (RingProgram.scalarProgram 3 t M cache) t).1
  simp only [wordCoefficientRun]
  nlinarith

variable {R K : Type*} [CommRing R] [CommRing K]

theorem wordCoefficientRun_indicator [DecidableEq K]
    (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (φ : ZMod (3^t) →+* R) (ρ : R →+* K)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    (∑ s : Fin t,
      (digitPolynomial (RingProgram.scalarRing 3 t M cache)
        (wordCoefficientRun t M cache).1 s).eval₂ φ x * hValue x^s.val) =
      if ρ x = 0 then 1 else 0 := by
  exact output_polynomial_indicator (RingProgram.scalarRing 3 t M cache) φ ρ t
    (halfRun (RingProgram.scalarProgram 3 t M cache) t).1
    (halfRun_inverse (RingProgram.scalarRing 3 t M cache)) q hq hker x hx

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

local instance ternaryPrimePrepared : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem literal_three_width : [true,true].length = Nat.log 2 3 + 1 := by
  rw [show Nat.log 2 3 = 1 from (Nat.log_eq_one_iff').2 (by decide)]
  rfl

/-- The ternary modulus is prepared from the fixed literal `[true,true]`. -/
def preparedWordCoefficientRun (t : ℕ) (ht : 0 < t) :
    (Fin (3*t) → RingProgram.ScalarCode 3 t) × ℕ :=
  let modulus := SubexpPreparedQuartic.prepareModulus 3 t [true,true] (by decide) literal_three_width
  let cache := RingProgram.prepareScalarCache 3 t modulus.1 ht
  let out := wordCoefficientRun t modulus.1 cache.1
  (out.1, modulus.2 + cache.2 + out.2)

theorem preparedWordCoefficientRun_cost (t : ℕ) (ht : 0 < t) :
    (preparedWordCoefficientRun t ht).2 ≤
      900*(t+1)^2 + 2*(3*baseWidth 3 t+1) +
      (3*t)^3*(36*scalarBudget 3 t+19) + 6*scalarBudget 3 t +
      t*(5*scalarBudget 3 t+8) + 8 +
      Nat.clog 2 t*(7*((3*t+1)^3*(3*scalarBudget 3 t+2))+8) := by
  let modulus := SubexpPreparedQuartic.prepareModulus 3 t [true,true] (by decide) literal_three_width
  let cache := RingProgram.prepareScalarCache 3 t modulus.1 ht
  have hm := SubexpPreparedQuartic.prepareModulus_cost_quadratic 3 t
    [true,true] (by decide) literal_three_width
  have hc := RingProgram.prepareScalarCache_cost 3 t modulus.1 ht
  have ho := wordCoefficientRun_cost t modulus.1 cache.1
  change modulus.2 + cache.2 + (wordCoefficientRun t modulus.1 cache.1).2 ≤ _
  change modulus.2 ≤ 100*(t+1)^2*([true,true].length+1)^2 at hm
  norm_num at hm
  dsimp [cache] at hc ⊢
  nlinarith

variable {R K : Type*} [CommRing R] [CommRing K]

/-- Full construction from t: the modulus, small constants, inverse of two,
multiplication table, and Newton lift are all generated explicitly. -/
theorem preparedWordCoefficientRun_indicator [DecidableEq K]
    (t : ℕ) (ht : 0 < t) (φ : ZMod (3^t) →+* R) (ρ : R →+* K)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    (∑ s : Fin t,
      (∑ a : Fin 3,
        φ (wordValue 3 t ((preparedWordCoefficientRun t ht).1 (digitIndex s a))) * x^a.val) *
      hValue x^s.val) = if ρ x = 0 then 1 else 0 := by
  let modulus := SubexpPreparedQuartic.prepareModulus 3 t [true,true] (by decide) literal_three_width
  let cache := RingProgram.prepareScalarCache 3 t modulus.1 ht
  have h := wordCoefficientRun_indicator t modulus.1 cache.1 φ ρ q hq hker x hx
  simp only [digitPolynomial_eval, digitValue, digitCode, RingProgram.scalarRing] at h
  exact h

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

/-- Flat output has exactly three degree-below-three coefficients per digit,
with each scalar occupying 2t bits. -/
theorem preparedWordOutput_length (t : ℕ) (ht : 0 < t) :
    (RingProgram.flat (preparedWordCoefficientRun t ht).1).length = 6*t^2 := by
  rw [RingProgram.flat_length, RingProgram.ternary_baseWidth]
  ring

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Table serialization is k-major, then i, with j fastest, matching the
native expansion/contraction service. -/
def tableWords {d B : ℕ} (table : Fin d → Fin d → Fin d → Word B) : List (Word B) :=
  (List.ofFn fun k : Fin d =>
    (List.ofFn fun i : Fin d => List.ofFn fun j : Fin d => table i j k).flatten).flatten

def tableTape {d B : ℕ} (table : Fin d → Fin d → Fin d → Word B) : List Bool :=
  ((tableWords table).map Subtype.val).flatten

@[simp] theorem tableWords_length {d B : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) : (tableWords table).length = d^3 := by
  simp [tableWords, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  ring

@[simp] theorem tableTape_length {d B : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) : (tableTape table).length = d^3*B := by
  have hlen : ∀ xs : List (Word B), ((xs.map Subtype.val).flatten).length = xs.length*B := by
    intro xs
    induction xs with
    | nil => simp
    | cons a xs ih =>
        simp only [List.map_cons, List.flatten_cons, List.length_append,
          List.length_cons, ih, a.property, Nat.add_mul, Nat.one_mul]
        omega
  rw [tableTape, hlen, tableWords_length]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
