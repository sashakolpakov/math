import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramArrays

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

/-- The initial H-adic vector is `(2u,-3u,u)` in its first digit. -/
def initialRun (ops : RingProgram C) (t : ℕ) (u : C) : (Fin (3*t) → C) × ℕ :=
  let zero := ops.zeroRun
  let twice := ops.addRun u u
  let three := ops.addRun twice.1 u
  let minusThree := ops.negRun three.1
  (fun k => if k.val = 0 then twice.1 else if k.val = 1 then minusThree.1
    else if k.val = 2 then u else zero.1,
    zero.2 + twice.2 + three.2 + minusThree.2 + 3*t + 4)

theorem initialRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (t : ℕ) (u : C) :
    (initialRun ops t u).2 ≤ 4*q + 3*t + 4 := by
  have h₀ := hq.zero
  have h₁ := hq.add u u
  have h₂ := hq.add (ops.addRun u u).1 u
  have h₃ := hq.neg (ops.addRun (ops.addRun u u).1 u).1
  simp only [initialRun]
  omega

/-- General coefficient version of the atom evaluation lemma. -/
theorem atom_eval (t s a : ℕ) (c x : R) (ha : a < 3) (ht : hValue x ^ t = 0) :
    (∑ k : Fin (3*t), (if k.val = 3*s+a then c else 0) * hadicBasis t x k) =
      c * (x^a * hValue x^s) := by
  have h := atomInteger_eval t s a 1 x ha ht
  simp only [Int.cast_one, one_mul] at h
  calc
    _ = c * (∑ k : Fin (3*t), (atomInteger (3*s+a) 1 k : R) * hadicBasis t x k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.val = 3*s+a <;> simp [atomInteger, hk]
    _ = _ := by rw [h]

theorem initialRun_correct (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) (u : C) :
    evaluate ops φ t x (initialRun ops.program t u).1 =
      Idempotent.initialValue (φ (ops.decode u)) x := by
  let c := φ (ops.decode u)
  have heval : evaluate ops φ t x (initialRun ops.program t u).1 =
      (∑ k : Fin (3*t), (if k.val = 0 then 2*c else 0) * hadicBasis t x k) +
      (∑ k : Fin (3*t), (if k.val = 1 then -(3*c) else 0) * hadicBasis t x k) +
      (∑ k : Fin (3*t), (if k.val = 2 then c else 0) * hadicBasis t x k) := by
    simp only [evaluate, RingProgram.denote, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [initialRun]
    by_cases h0 : k.val = 0
    · simp [h0, ops.add_correct, map_add, c]
      ring
    · by_cases h1 : k.val = 1
      · simp [ h1, ops.add_correct,
          ops.neg_correct, map_add, map_neg, c]
        ring
      · by_cases h2 : k.val = 2
        · simp [ h2, c]
        · simp [h0, h1, h2, ops.zero_correct]
  rw [heval]
  have h0 := atom_eval t 0 0 (2*c) x (by omega) ht
  have h1 := atom_eval t 0 1 (-(3*c)) x (by omega) ht
  have h2 := atom_eval t 0 2 c x (by omega) ht
  simp only [Nat.mul_zero, Nat.zero_add, pow_zero, mul_one ] at h0 h1 h2
  rw [h0, h1, h2]
  dsimp [Idempotent.initialValue, c]
  ring

/-- Complete finite array construction, with a measured initial stage. -/
def coefficientRun (ops : RingProgram C) (t : ℕ) (u : C) : (Fin (3*t) → C) × ℕ :=
  let setup := tableConstructionRun ops t
  let initial := initialRun ops t u
  let program := RingProgram.program ops setup.1 (zeroCode ops t) (oneCode ops t)
  let out := liftRun program initial.1 t
  (out.1, setup.2 + initial.2 + out.2 + 1)

theorem coefficientRun_correct (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) (u : C) :
    evaluate ops φ t x (coefficientRun ops.program t u).1 =
      Idempotent.iterate (Idempotent.initialValue (φ (ops.decode u)) x) (Nat.clog 2 t) := by
  have h := liftRun_correct (arrayRepresented ops φ t x ht) (initialRun ops.program t u).1 t
  simp only [arrayRepresented_program, arrayRepresented_decode] at h
  change evaluate ops φ t x
    (liftRun (arrayProgram ops.program t) (initialRun ops.program t u).1 t).1 = _
  simpa only [initialRun_correct ops φ t x ht] using h

theorem coefficientRun_cost (ops : RingProgram C) {q : ℕ}
    (hq : ProgramBudget ops q) (t : ℕ) (u : C) :
    (coefficientRun ops t u).2 ≤
      (3*t)^3*(36*q+19) + 4*q + 3*t + 7 +
        Nat.clog 2 t * (7*((3*t+1)^3*(3*q+2))+8) := by
  have h₀ := tableConstructionRun_cost ops hq t
  have h₁ := initialRun_cost ops hq t u
  have h₂ := arrayLift_cost ops hq t (initialRun ops t u).1
  change (tableConstructionRun ops t).2 + (initialRun ops t u).2 +
    (liftRun (arrayProgram ops t) (initialRun ops t u).1 t).2 + 1 ≤ _
  omega

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

/-- The public output is `t` triples, in increasing H-adic order. -/
def digitIndex {t : ℕ} (s : Fin t) (a : Fin 3) : Fin (3*t) :=
  ⟨3*s.val+a.val, by have := s.isLt; have := a.isLt; omega⟩

def digitCode {t : ℕ} (v : Fin (3*t) → C) (s : Fin t) (a : Fin 3) : C :=
  v (digitIndex s a)

def digitValue (ops : RepresentedRing C A) (φ : A →+* R) {t : ℕ}
    (v : Fin (3*t) → C) (s : Fin t) (x : R) : R :=
  ∑ a : Fin 3, φ (ops.decode (digitCode v s a)) * x^a.val

def digitEquiv (t : ℕ) : Fin t × Fin 3 ≃ Fin (3*t) :=
  (finProdFinEquiv : Fin t × Fin 3 ≃ Fin (t*3)).trans (finCongr (Nat.mul_comm t 3))

@[simp] theorem digitEquiv_apply (t : ℕ) (s : Fin t) (a : Fin 3) :
    digitEquiv t (s,a) = digitIndex s a := by
  apply Fin.ext
  simp [digitEquiv, digitIndex, finProdFinEquiv]
  omega

theorem evaluate_digits (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (v : Fin (3*t) → C) :
    evaluate ops φ t x v = ∑ s : Fin t, digitValue ops φ v s x * hValue x^s.val := by
  rw [evaluate, RingProgram.denote, ← (digitEquiv t).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  simp only [digitValue, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  have hmod : (digitIndex s a).val % 3 = a.val := by
    dsimp [digitIndex]; have := a.isLt; omega
  have hdiv : (digitIndex s a).val / 3 = s.val := by
    dsimp [digitIndex]; have := a.isLt; omega
  simp only [digitEquiv_apply, hadicBasis, hmod, hdiv, digitCode]
  ring

/-- The finite algorithm produces exactly the desired zero-residue indicator. -/
theorem coefficientRun_indicator [DecidableEq K]
    (ops : RepresentedRing C A) (φ : A →+* R) (ρ : R →+* K)
    (t : ℕ) (u : C) (hu : 2*ops.decode u = 1)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    evaluate ops φ t x (coefficientRun ops.program t u).1 =
      if ρ x = 0 then 1 else 0 := by
  have hH : hValue x^t = 0 := by
    simpa only [Idempotent.eval_ternaryH, hValue] using
      Idempotent.eval_H_nilpotent φ ρ q t hker hq x hx
  rw [coefficientRun_correct ops φ t x hH]
  have huR : 2*φ (ops.decode u) = 1 := Idempotent.mapped_inverse_two φ hu
  have huK : 2*ρ (φ (ops.decode u)) = 1 := Idempotent.mapped_inverse_two ρ huR
  have herr : hValue x ∣
      (Idempotent.initialValue (φ (ops.decode u)) x)^2 -
        Idempotent.initialValue (φ (ops.decode u)) x := by
    rw [Idempotent.initialValue_error _ _ huR]
    exact dvd_mul_right _ _
  have he := Idempotent.iterate_idempotent herr hH (Nat.le_pow_clog (by decide) t)
  by_cases hz : ρ x = 0
  · simp only [hz, ↓reduceIte]
    have hi : ρ (Idempotent.initialValue (φ (ops.decode u)) x) = 1 := by
      rw [Idempotent.map_initialValue, hz]
      exact Idempotent.initialValue_zero _ huK
    apply Idempotent.idempotent_one_of_residue ρ hker he hq
    rw [Idempotent.iterate_residue ρ (by rw [hi]; ring), hi]
  · simp only [hz, ↓reduceIte]
    have hi : ρ (Idempotent.initialValue (φ (ops.decode u)) x) = 0 := by
      rw [Idempotent.map_initialValue]
      rcases hx.resolve_left hz with h | h <;> rw [h] <;> simp
    apply Idempotent.idempotent_zero_of_residue ρ hker he hq
    rw [Idempotent.iterate_residue ρ (by rw [hi]; ring), hi]

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

/-- A semantic view of three stored coefficients, not an implementation step. -/
noncomputable def digitPolynomial (ops : RepresentedRing C A) {t : ℕ}
    (v : Fin (3*t) → C) (s : Fin t) : Polynomial A :=
  ∑ a : Fin 3, Polynomial.monomial a.val (ops.decode (digitCode v s a))

theorem digitPolynomial_degree (ops : RepresentedRing C A) {t : ℕ}
    (v : Fin (3*t) → C) (s : Fin t) :
    (digitPolynomial ops v s).natDegree < 3 := by
  have h : (digitPolynomial ops v s).natDegree ≤ 2 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a _
    exact (Polynomial.natDegree_monomial_le _).trans (by have := a.isLt; omega)
  omega

theorem digitPolynomial_eval (ops : RepresentedRing C A) (φ : A →+* R) {t : ℕ}
    (v : Fin (3*t) → C) (s : Fin t) (x : R) :
    (digitPolynomial ops v s).eval₂ φ x = digitValue ops φ v s x := by
  simp only [digitPolynomial, digitValue, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial]

theorem output_polynomial_indicator [DecidableEq K]
    (ops : RepresentedRing C A) (φ : A →+* R) (ρ : R →+* K)
    (t : ℕ) (u : C) (hu : 2*ops.decode u = 1)
    (q : R) (hq : q^t = 0) (hker : ∀ y, ρ y = 0 → q ∣ y)
    (x : R) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    (∑ s : Fin t, (digitPolynomial ops (coefficientRun ops.program t u).1 s).eval₂ φ x *
      hValue x^s.val) = if ρ x = 0 then 1 else 0 := by
  simp only [digitPolynomial_eval]
  rw [← evaluate_digits]
  exact coefficientRun_indicator ops φ ρ t u hu q hq hker x hx

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
