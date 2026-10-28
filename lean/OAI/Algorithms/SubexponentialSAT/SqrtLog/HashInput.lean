import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SAT
import OAI.Algorithms.SubexponentialSAT.Incidence

namespace OAI.Algorithms

/-! Actual clause violations and sparse hash factors on the original variables. -/

namespace SubexponentialSAT.SqrtLog.HashInput


open scoped BigOperators
noncomputable section

variable {V E I R : Type*} [DecidableEq V] [CommRing R]

def boolValue (b : Bool) : R := if b then 1 else 0

def clauseValue (C : SAT.Clause V) (x : SAT.Assignment V) : R :=
  if C.eval x then 0 else 1

def falsifyingLiteral (l : SAT.Literal V) : MvPolynomial V R :=
  if l.positive then 1 - MvPolynomial.X l.variable else MvPolynomial.X l.variable

def clauseViolation (C : SAT.Clause V) : MvPolynomial V R :=
  ∏ l ∈ C, falsifyingLiteral l

omit [DecidableEq V] in
@[simp] theorem eval_falsifyingLiteral (l : SAT.Literal V) (x : SAT.Assignment V) :
    MvPolynomial.eval (fun v => boolValue (R := R) (x v)) (falsifyingLiteral l) =
      if l.eval x then 0 else 1 := by
  rcases l with ⟨v, p⟩
  cases p <;> cases h : x v <;>
    simp [falsifyingLiteral, boolValue, SAT.Literal.eval, h]

@[simp] theorem eval_clauseViolation (C : SAT.Clause V) (x : SAT.Assignment V) :
    MvPolynomial.eval (fun v => boolValue (R := R) (x v)) (clauseViolation C) =
      clauseValue C x := by
  induction C using Finset.induction_on with
  | empty => simp [clauseViolation, clauseValue]
  | @insert l C hl ih =>
      simp only [clauseViolation, Finset.prod_insert hl, map_mul] at ih ⊢
      rw [eval_falsifyingLiteral, ih]
      cases h1 : l.eval x <;> cases h2 : SAT.Clause.eval x C <;>
        simp [clauseValue, SAT.Clause.eval_insert, h1, h2]

def clauseScope (C : SAT.Clause V) : Finset V := C.image SAT.Literal.variable

theorem card_clauseScope_le (C : SAT.Clause V) : (clauseScope C).card ≤ C.card :=
  Finset.card_image_le

section Nontrivial
variable [Nontrivial R]

omit [DecidableEq V] in
theorem totalDegree_falsifyingLiteral (l : SAT.Literal V) :
    (falsifyingLiteral (R := R) l).totalDegree ≤ 1 := by
  unfold falsifyingLiteral
  split_ifs
  · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
  · simp

omit [DecidableEq V] in
theorem totalDegree_clauseViolation (C : SAT.Clause V) :
    (clauseViolation (R := R) C).totalDegree ≤ C.card := by
  calc
    _ ≤ ∑ l ∈ C, (falsifyingLiteral (R := R) l).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _l ∈ C, 1 := Finset.sum_le_sum fun l _ => totalDegree_falsifyingLiteral l
    _ = _ := by simp

theorem vars_falsifyingLiteral (l : SAT.Literal V) :
    (falsifyingLiteral (R := R) l).vars ⊆ {l.variable} := by
  unfold falsifyingLiteral
  split_ifs
  · exact (MvPolynomial.vars_sub_subset (1 : MvPolynomial V R)).trans (by simp)
  · simp

theorem vars_clauseViolation (C : SAT.Clause V) :
    (clauseViolation (R := R) C).vars ⊆ clauseScope C := by
  intro v hv
  obtain ⟨l, hl, hv⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_prod _ hv)
  have hvl : v = l.variable := Finset.mem_singleton.mp (vars_falsifyingLiteral l hv)
  exact Finset.mem_image.mpr ⟨l, hl, hvl.symm⟩

end Nontrivial

section Hash
variable [Fintype E] [DecidableEq E]

def rowSupport (h : E → R) : Finset E := by
  classical
  exact Finset.univ.filter fun e => h e ≠ 0

def hashScope (C : E → SAT.Clause V) (h : E → R) : Finset V :=
  (rowSupport h).biUnion fun e => clauseScope (C e)

def hashPolynomial (C : E → SAT.Clause V) (h : E → R) : MvPolynomial V R :=
  ∑ e, MvPolynomial.C (h e) * clauseViolation (C e)

def violationVector (C : E → SAT.Clause V) (x : SAT.Assignment V) : E → R :=
  fun e => clauseValue (C e) x

def violationWeight (C : E → SAT.Clause V) (x : SAT.Assignment V) : ℕ :=
  ∑ e, if (C e).eval x then 0 else 1

omit [DecidableEq V] [DecidableEq E] in
theorem violationWeight_le (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight C x ≤ Fintype.card E := by
  calc
    _ ≤ ∑ _e : E, 1 := Finset.sum_le_sum fun e _ => by split_ifs <;> omega
    _ = _ := by simp

omit [DecidableEq E] in
omit [DecidableEq V] in
theorem violationWeight_eq_zero_iff (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight C x = 0 ↔ ∀ e, (C e).eval x = true := by
  simp [violationWeight, Finset.sum_eq_zero_iff]

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem violationVector_of_satisfied (C : E → SAT.Clause V) (x : SAT.Assignment V)
    (hx : ∀ e, (C e).eval x = true) : violationVector (R := R) C x = 0 := by
  funext e
  simp [violationVector, clauseValue, hx e]

omit [Fintype E] [DecidableEq E] in
omit [DecidableEq V] in
theorem violationVector_eq_zero_iff [Nontrivial R] (C : E → SAT.Clause V)
    (x : SAT.Assignment V) :
    violationVector (R := R) C x = 0 ↔ ∀ e, (C e).eval x = true := by
  simp [funext_iff, violationVector, clauseValue]

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem violationVector_zero_or_one (C : E → SAT.Clause V) (x : SAT.Assignment V) (e : E) :
    violationVector (R := R) C x e = 0 ∨ violationVector (R := R) C x e = 1 := by
  cases he : (C e).eval x <;> simp [violationVector, clauseValue, he]

omit [DecidableEq E] in
omit [DecidableEq V] in
theorem sum_violationVector_eq_weight (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    (∑ e, violationVector (R := R) C x e) = (violationWeight C x : R) := by
  simp [violationVector, clauseValue, violationWeight]

omit [DecidableEq V] [DecidableEq E] in
theorem hashPolynomial_eq_sum_rowSupport (C : E → SAT.Clause V) (h : E → R) :
    hashPolynomial C h =
      ∑ e ∈ rowSupport h, MvPolynomial.C (h e) * clauseViolation (C e) := by
  classical
  rw [hashPolynomial, rowSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : h e = 0 <;> simp [he]

omit [DecidableEq E] in
@[simp] theorem eval_hashPolynomial (C : E → SAT.Clause V) (h : E → R)
    (x : SAT.Assignment V) :
    MvPolynomial.eval (fun v => boolValue (R := R) (x v)) (hashPolynomial C h) =
      ∑ e, h e * violationVector C x e := by
  simp [hashPolynomial, violationVector]

omit [DecidableEq E] in
theorem card_hashScope_le (C : E → SAT.Clause V) (h : E → R) (k : ℕ)
    (hwidth : ∀ e, (C e).card ≤ k) :
    (hashScope C h).card ≤ k * (rowSupport h).card := by
  calc
    _ ≤ ∑ e ∈ rowSupport h, (clauseScope (C e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ rowSupport h, k :=
      Finset.sum_le_sum fun e _ => (card_clauseScope_le _).trans (hwidth e)
    _ = _ := by simp [Nat.mul_comm]

omit [DecidableEq E] in
theorem total_hashScope_le [Fintype I] (C : E → SAT.Clause V) (A : I → E → R)
    (k : ℕ) (hwidth : ∀ e, (C e).card ≤ k) :
    ∑ i, (hashScope C (A i)).card ≤ k * ∑ i, (rowSupport (A i)).card := by
  calc
    _ ≤ ∑ i, k * (rowSupport (A i)).card :=
      Finset.sum_le_sum fun i _ => card_hashScope_le C (A i) k hwidth
    _ = _ := (Finset.mul_sum ..).symm

omit [DecidableEq E] in
omit [DecidableEq V] in
theorem totalDegree_hashPolynomial [Nontrivial R] (C : E → SAT.Clause V)
    (h : E → R) (k : ℕ) (hwidth : ∀ e, (C e).card ≤ k) :
    (hashPolynomial C h).totalDegree ≤ k := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa using (totalDegree_clauseViolation (R := R) (C e)).trans (hwidth e))

omit [DecidableEq E] in
theorem vars_hashPolynomial [Nontrivial R] (C : E → SAT.Clause V) (h : E → R) :
    (hashPolynomial C h).vars ⊆ hashScope C h := by
  intro v hv
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hv)
  have hn : h e ≠ 0 := by
    intro hz
    simp [hz] at he
  have hc : v ∈ clauseScope (C e) := by
    have hm := MvPolynomial.vars_mul (MvPolynomial.C (h e)) (clauseViolation (C e)) he
    simp only [MvPolynomial.vars_C, Finset.empty_union] at hm
    exact vars_clauseViolation _ hm
  exact Finset.mem_biUnion.mpr ⟨e, by simp [rowSupport, hn], hc⟩

omit [DecidableEq E] in
theorem eval₂_hashPolynomial_congr [Nontrivial R] {S : Type*} [CommRing S]
    (C : E → SAT.Clause V) (h : E → R) (f : R →+* S) (x y : V → S)
    (hxy : ∀ v ∈ hashScope C h, x v = y v) :
    MvPolynomial.eval₂ f x (hashPolynomial C h) =
      MvPolynomial.eval₂ f y (hashPolynomial C h) := by
  exact MvPolynomial.eval₂Hom_congr' rfl
    (fun v hv _ => hxy v (vars_hashPolynomial C h hv)) rfl

/-- The existing finite CNF syntax supplies an indexed family without a new syntax. -/
def cnfClauses (F : SAT.CNF V) : F → SAT.Clause V := fun e => e.val

omit [DecidableEq V] in
theorem violationWeight_cnf_eq_zero_iff (F : SAT.CNF V) (x : SAT.Assignment V) :
    violationWeight (cnfClauses F) x = 0 ↔ F.eval x = true := by
  rw [violationWeight_eq_zero_iff, SAT.CNF.eval_eq_true]
  simp [cnfClauses]

end Hash
end
end SubexponentialSAT.SqrtLog.HashInput

end OAI.Algorithms
