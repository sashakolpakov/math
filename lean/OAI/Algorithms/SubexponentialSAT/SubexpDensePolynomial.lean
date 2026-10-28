import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Dense univariate arithmetic through represented coefficient callbacks

Code words need no ring structure. Every scalar operation is a call to the
supplied implementation, and the returned counters are added along the actual
execution. These are callback counters, not a primitive-machine runtime theorem.
-/

namespace SubexponentialSAT.SubexpDensePolynomial

variable {C R : Type*} [CommRing R] (ops : SubexpSymbolicCost.RepresentedRing C R)

def decodeList (P : List C) : List R := P.map ops.decode

@[simp] theorem decodeList_length (P : List C) : (decodeList ops P).length = P.length := by
  simp [decodeList]

def addRun : List C → List C → List C × ℕ
  | [], Q => (Q, 0)
  | P, [] => (P, 0)
  | a :: P, b :: Q =>
      let head := ops.addRun a b
      let rest := addRun P Q
      (head.1 :: rest.1, head.2 + rest.2)

def scaleRun (a : C) : List C → List C × ℕ
  | [] => ([], 0)
  | b :: P =>
      let head := ops.mulRun a b
      let rest := scaleRun a P
      (head.1 :: rest.1, head.2 + rest.2)

def mulRun : List C → List C → List C × ℕ
  | [], _ => ([], 0)
  | a :: P, Q =>
      let row := scaleRun ops a Q
      let rest := mulRun P Q
      let zero := ops.zeroRun
      let out := addRun ops row.1 (zero.1 :: rest.1)
      (out.1, row.2 + rest.2 + zero.2 + out.2)

def negRun : List C → List C × ℕ
  | [] => ([], 0)
  | a :: P =>
      let head := ops.negRun a
      let rest := negRun P
      (head.1 :: rest.1, head.2 + rest.2)

def evalRun (x : C) : List C → C × ℕ
  | [] => ops.zeroRun
  | a :: P =>
      let rest := evalRun x P
      let product := ops.mulRun x rest.1
      let out := ops.addRun a product.1
      (out.1, rest.2 + product.2 + out.2)

def shiftRun (a : C) : List C → List C × ℕ
  | [] => ([], 0)
  | b :: P =>
      let rest := shiftRun a P
      let one := ops.oneRun
      let product := mulRun ops [a, one.1] rest.1
      let out := addRun ops [b] product.1
      (out.1, rest.2 + one.2 + product.2 + out.2)

def sumRun : List (List C) → List C × ℕ
  | [] => ([], 0)
  | P :: Ps =>
      let rest := sumRun Ps
      let out := addRun ops P rest.1
      (out.1, rest.2 + out.2)

def productRun : List (List C) → List C × ℕ
  | [] => ([ops.oneRun.1], ops.oneRun.2)
  | P :: Ps =>
      let rest := productRun Ps
      let out := mulRun ops P rest.1
      (out.1, rest.2 + out.2)

def truncateRun (D : ℕ) (P : List C) : List C × ℕ := (P.take D, 0)

theorem addRun_correct (P Q : List C) :
    decodeList ops (addRun ops P Q).1 =
      PolynomialAlgorithm.add (decodeList ops P) (decodeList ops Q) := by
  induction P generalizing Q with
  | nil => simp [addRun, decodeList, PolynomialAlgorithm.add, PolynomialAlgorithm.addWithCost]
  | cons a P ih =>
      cases Q with
      | nil => simp [addRun, decodeList, PolynomialAlgorithm.add, PolynomialAlgorithm.addWithCost]
      | cons b Q =>
          simp only [addRun, decodeList, List.map_cons, ops.add_correct]
          change (ops.decode a + ops.decode b) :: decodeList ops (addRun ops P Q).1 = _
          rw [ih]
          rfl

theorem scaleRun_correct (a : C) (P : List C) :
    decodeList ops (scaleRun ops a P).1 =
      PolynomialAlgorithm.scale (ops.decode a) (decodeList ops P) := by
  induction P with
  | nil => rfl
  | cons b P ih =>
      change ops.decode (ops.mulRun a b).1 :: decodeList ops (scaleRun ops a P).1 = _
      rw [ops.mul_correct, ih]
      rfl

theorem mulRun_correct (P Q : List C) :
    decodeList ops (mulRun ops P Q).1 =
      PolynomialAlgorithm.mul (decodeList ops P) (decodeList ops Q) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      change decodeList ops (addRun ops _ _).1 = _
      rw [addRun_correct, scaleRun_correct]
      change PolynomialAlgorithm.add _ (ops.decode ops.zeroRun.1 ::
        decodeList ops (mulRun ops P Q).1) = _
      rw [ops.zero_correct, ih]
      rfl

theorem negRun_correct (P : List C) :
    decodeList ops (negRun ops P).1 = (decodeList ops P).map Neg.neg := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      change ops.decode (ops.negRun a).1 :: decodeList ops (negRun ops P).1 = _
      rw [ops.neg_correct, ih]
      rfl

theorem evalRun_correct (x : C) (P : List C) :
    ops.decode (evalRun ops x P).1 = PolynomialAlgorithm.eval (ops.decode x) (decodeList ops P) := by
  induction P with
  | nil => exact ops.zero_correct
  | cons a P ih =>
      change ops.decode (ops.addRun a (ops.mulRun x (evalRun ops x P).1).1).1 = _
      rw [ops.add_correct, ops.mul_correct, ih]
      rfl

theorem shiftRun_correct (a : C) (P : List C) :
    decodeList ops (shiftRun ops a P).1 =
      PolynomialAlgorithm.shift (ops.decode a) (decodeList ops P) := by
  induction P with
  | nil => rfl
  | cons b P ih =>
      change decodeList ops (addRun ops _ _).1 = _
      rw [addRun_correct, mulRun_correct, ih]
      simp only [decodeList, List.map_cons, List.map_nil, ops.one_correct]
      rfl

theorem sumRun_correct (Ps : List (List C)) :
    decodeList ops (sumRun ops Ps).1 =
      PolynomialAlgorithm.sum (Ps.map (decodeList ops)) := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih =>
      change decodeList ops (addRun ops _ _).1 = _
      rw [addRun_correct, ih]
      rfl

theorem productRun_correct (Ps : List (List C)) :
    decodeList ops (productRun ops Ps).1 =
      PolynomialAlgorithm.product (Ps.map (decodeList ops)) := by
  induction Ps with
  | nil => simp [productRun, decodeList, ops.one_correct,
      PolynomialAlgorithm.product, PolynomialAlgorithm.productWithCost]
  | cons P Ps ih =>
      change decodeList ops (mulRun ops _ _).1 = _
      rw [mulRun_correct, ih]
      rfl

theorem truncateRun_correct (D : ℕ) (P : List C) :
    decodeList ops (truncateRun D P).1 = PolynomialAlgorithm.truncate D (decodeList ops P) := by
  simp [decodeList, truncateRun, PolynomialAlgorithm.truncate]

@[simp] theorem addRun_length (P Q : List C) :
    (addRun ops P Q).1.length = max P.length Q.length := by
  rw [← decodeList_length ops, addRun_correct, PolynomialAlgorithm.length_add]
  simp

@[simp] theorem scaleRun_length (a : C) (P : List C) :
    (scaleRun ops a P).1.length = P.length := by
  rw [← decodeList_length ops, scaleRun_correct, PolynomialAlgorithm.length_scale]
  simp

theorem mulRun_length (P Q : List C) :
    (mulRun ops P Q).1.length ≤ P.length + Q.length := by
  rw [← decodeList_length ops, mulRun_correct]
  simpa using PolynomialAlgorithm.length_mul_le (decodeList ops P) (decodeList ops Q)

@[simp] theorem negRun_length (P : List C) : (negRun ops P).1.length = P.length := by
  rw [← decodeList_length ops, negRun_correct, List.length_map]
  simp

theorem shiftRun_length (a : C) (P : List C) :
    (shiftRun ops a P).1.length ≤ 2 * P.length := by
  rw [← decodeList_length ops, shiftRun_correct]
  simpa using PolynomialAlgorithm.length_shift_le (ops.decode a) (decodeList ops P)

theorem sumRun_length (Ps : List (List C)) (L : ℕ) (h : ∀ P ∈ Ps, P.length ≤ L) :
    (sumRun ops Ps).1.length ≤ L := by
  rw [← decodeList_length ops, sumRun_correct]
  apply PolynomialAlgorithm.sumWithCost_length_le
  intro Q hQ
  obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hQ
  simpa using h P hP

theorem productRun_length (Ps : List (List C)) (L : ℕ) (h : ∀ P ∈ Ps, P.length ≤ L) :
    (productRun ops Ps).1.length ≤ 1 + Ps.length * L := by
  rw [← decodeList_length ops, productRun_correct]
  have hp := PolynomialAlgorithm.productWithCost_length_le (Ps.map (decodeList ops)) L (by
    intro Q hQ
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hQ
    simpa using h P hP)
  simpa [PolynomialAlgorithm.product] using hp

variable {q : ℕ} (budget : SubexpSymbolicCost.ScalarBudget ops q)

include budget

theorem addRun_cost (P Q : List C) : (addRun ops P Q).2 ≤ min P.length Q.length * q := by
  induction P generalizing Q with
  | nil => simp [addRun]
  | cons a P ih =>
      cases Q with
      | nil => simp [addRun]
      | cons b Q =>
          have hh := budget.add a b
          have ht := ih Q
          simpa [addRun, Nat.add_mul, Nat.add_comm] using Nat.add_le_add hh ht

theorem scaleRun_cost (a : C) (P : List C) : (scaleRun ops a P).2 ≤ P.length * q := by
  induction P with
  | nil => simp [scaleRun]
  | cons b P ih =>
      simpa [scaleRun, Nat.add_mul, Nat.add_comm] using Nat.add_le_add (budget.mul a b) ih

theorem mulRun_cost (P Q : List C) :
    (mulRun ops P Q).2 ≤ (2 * P.length * Q.length + P.length) * q := by
  induction P with
  | nil => simp [mulRun]
  | cons a P ih =>
      have hr := scaleRun_cost ops budget a Q
      have ha := (addRun_cost ops budget (scaleRun ops a Q).1
        (ops.zeroRun.1 :: (mulRun ops P Q).1)).trans
        (Nat.mul_le_mul_right q (Nat.min_le_left _ _))
      rw [scaleRun_length] at ha
      have hz := budget.zero
      change _ + _ + _ + _ ≤ _
      calc
        _ ≤ Q.length * q + (2 * P.length * Q.length + P.length) * q + q + Q.length * q :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hr ih) hz) ha
        _ = _ := by simp only [List.length_cons]; ring

theorem negRun_cost (P : List C) : (negRun ops P).2 ≤ P.length * q := by
  induction P with
  | nil => simp [negRun]
  | cons a P ih =>
      simpa [negRun, Nat.add_mul, Nat.add_comm] using Nat.add_le_add (budget.neg a) ih

theorem evalRun_cost (x : C) (P : List C) :
    (evalRun ops x P).2 ≤ (2 * P.length + 1) * q := by
  induction P with
  | nil => simpa [evalRun] using budget.zero
  | cons a P ih =>
      have hm := budget.mul x (evalRun ops x P).1
      have ha := budget.add a (ops.mulRun x (evalRun ops x P).1).1
      change _ + _ + _ ≤ _
      calc
        _ ≤ (2 * P.length + 1) * q + q + q := Nat.add_le_add (Nat.add_le_add ih hm) ha
        _ = _ := by simp only [List.length_cons]; ring

theorem shiftRun_cost (a : C) (P : List C) :
    (shiftRun ops a P).2 ≤ 4 * P.length ^ 2 * q := by
  induction P with
  | nil => simp [shiftRun]
  | cons b P ih =>
      have hl := shiftRun_length ops a P
      have hm := mulRun_cost ops budget [a, ops.oneRun.1] (shiftRun ops a P).1
      have hm' : (mulRun ops [a, ops.oneRun.1] (shiftRun ops a P).1).2 ≤
          (8 * P.length + 2) * q := by
        apply hm.trans
        apply Nat.mul_le_mul_right q
        simp only [List.length_cons, List.length_nil] at ⊢
        omega
      have ha := (addRun_cost ops budget [b]
        (mulRun ops [a, ops.oneRun.1] (shiftRun ops a P).1).1).trans
        (Nat.mul_le_mul_right q (Nat.min_le_left _ _))
      simp only [List.length_cons, List.length_nil, Nat.zero_add, one_mul] at ha
      have ho := budget.one
      change _ + _ + _ + _ ≤ _
      calc
        _ ≤ 4 * P.length ^ 2 * q + q + (8 * P.length + 2) * q + q :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ih ho) hm') ha
        _ = _ := by simp only [List.length_cons]; ring

theorem sumRun_cost (Ps : List (List C)) (L : ℕ) (h : ∀ P ∈ Ps, P.length ≤ L) :
    (sumRun ops Ps).2 ≤ Ps.length * L * q := by
  induction Ps with
  | nil => simp [sumRun]
  | cons P Ps ih =>
      have hp := h P (by simp)
      have ht := ih (fun Q hQ => h Q (by simp [hQ]))
      have ha := (addRun_cost ops budget P (sumRun ops Ps).1).trans
        (Nat.mul_le_mul_right q ((Nat.min_le_left _ _).trans hp))
      change _ + _ ≤ _
      calc
        _ ≤ Ps.length * L * q + L * q := Nat.add_le_add ht ha
        _ = _ := by simp only [List.length_cons]; ring

theorem productRun_cost (Ps : List (List C)) (L : ℕ) (h : ∀ P ∈ Ps, P.length ≤ L) :
    (productRun ops Ps).2 ≤ (1 + 3 * Ps.length * L * (1 + Ps.length * L)) * q := by
  induction Ps with
  | nil => simpa [productRun] using budget.one
  | cons P Ps ih =>
      have hp := h P (by simp)
      have hs : ∀ Q ∈ Ps, Q.length ≤ L := fun Q hQ => h Q (by simp [hQ])
      have ht := ih hs
      have hl := productRun_length ops Ps L hs
      have hm := mulRun_cost ops budget P (productRun ops Ps).1
      have hm' : (mulRun ops P (productRun ops Ps).1).2 ≤
          (2 * L * (1 + Ps.length * L) + L) * q := by
        apply hm.trans
        gcongr
      change _ + _ ≤ _
      calc
        _ ≤ (1 + 3 * Ps.length * L * (1 + Ps.length * L)) * q +
            (2 * L * (1 + Ps.length * L) + L) * q := Nat.add_le_add ht hm'
        _ ≤ _ := by
          simp only [List.length_cons]
          ring_nf
          omega

end SubexponentialSAT.SubexpDensePolynomial

namespace SubexponentialSAT.SubexpDensePolynomial

section Programs

variable {C : Type*} (ops : SubexpSymbolicCost.RingProgram C)

def addProgram : List C → List C → List C × ℕ
  | [], Q => (Q, 0)
  | P, [] => (P, 0)
  | a :: P, b :: Q =>
      let head := ops.addRun a b
      let rest := addProgram P Q
      (head.1 :: rest.1, head.2 + rest.2)

def scaleProgram (a : C) : List C → List C × ℕ
  | [] => ([], 0)
  | b :: P =>
      let head := ops.mulRun a b
      let rest := scaleProgram a P
      (head.1 :: rest.1, head.2 + rest.2)

def mulProgram : List C → List C → List C × ℕ
  | [], _ => ([], 0)
  | a :: P, Q =>
      let row := scaleProgram ops a Q
      let rest := mulProgram P Q
      let zero := ops.zeroRun
      let out := addProgram ops row.1 (zero.1 :: rest.1)
      (out.1, row.2 + rest.2 + zero.2 + out.2)

def negProgram : List C → List C × ℕ
  | [] => ([], 0)
  | a :: P =>
      let head := ops.negRun a
      let rest := negProgram P
      (head.1 :: rest.1, head.2 + rest.2)

def evalProgram (x : C) : List C → C × ℕ
  | [] => ops.zeroRun
  | a :: P =>
      let rest := evalProgram x P
      let product := ops.mulRun x rest.1
      let out := ops.addRun a product.1
      (out.1, rest.2 + product.2 + out.2)

def shiftProgram (a : C) : List C → List C × ℕ
  | [] => ([], 0)
  | b :: P =>
      let rest := shiftProgram a P
      let one := ops.oneRun
      let product := mulProgram ops [a, one.1] rest.1
      let out := addProgram ops [b] product.1
      (out.1, rest.2 + one.2 + product.2 + out.2)

def sumProgram : List (List C) → List C × ℕ
  | [] => ([], 0)
  | P :: Ps =>
      let rest := sumProgram Ps
      let out := addProgram ops P rest.1
      (out.1, rest.2 + out.2)

def productProgram : List (List C) → List C × ℕ
  | [] => ([ops.oneRun.1], ops.oneRun.2)
  | P :: Ps =>
      let rest := productProgram Ps
      let out := mulProgram ops P rest.1
      (out.1, rest.2 + out.2)

end Programs

section ProgramRefinement

variable {C R : Type*} [CommRing R] (ops : SubexpSymbolicCost.RepresentedRing C R)

@[simp] theorem addProgram_run (P Q : List C) :
    addProgram ops.program P Q = addRun ops P Q := by
  induction P generalizing Q with
  | nil => simp [addProgram, addRun]
  | cons a P ih =>
      cases Q with
      | nil => rfl
      | cons b Q => simp only [addProgram, addRun, ih]

@[simp] theorem scaleProgram_run (a : C) (P : List C) :
    scaleProgram ops.program a P = scaleRun ops a P := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [scaleProgram, scaleRun, ih]

@[simp] theorem mulProgram_run (P Q : List C) :
    mulProgram ops.program P Q = mulRun ops P Q := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp only [mulProgram, mulRun, scaleProgram_run, addProgram_run, ih]

@[simp] theorem negProgram_run (P : List C) :
    negProgram ops.program P = negRun ops P := by
  induction P with
  | nil => rfl
  | cons a P ih => simp only [negProgram, negRun, ih]

@[simp] theorem evalProgram_run (x : C) (P : List C) :
    evalProgram ops.program x P = evalRun ops x P := by
  induction P with
  | nil => rfl
  | cons a P ih => simp only [evalProgram, evalRun, ih]

@[simp] theorem shiftProgram_run (a : C) (P : List C) :
    shiftProgram ops.program a P = shiftRun ops a P := by
  induction P with
  | nil => rfl
  | cons b P ih =>
      simp only [shiftProgram, shiftRun, mulProgram_run, addProgram_run, ih]

@[simp] theorem sumProgram_run (Ps : List (List C)) :
    sumProgram ops.program Ps = sumRun ops Ps := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih => simp [sumProgram, sumRun, ih]

@[simp] theorem productProgram_run (Ps : List (List C)) :
    productProgram ops.program Ps = productRun ops Ps := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih => simp [productProgram, productRun, ih]

end ProgramRefinement

end SubexponentialSAT.SubexpDensePolynomial

end OAI.Algorithms
