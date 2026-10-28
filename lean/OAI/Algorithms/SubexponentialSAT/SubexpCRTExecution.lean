import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpResidueInverse
import OAI.Algorithms.SubexponentialSAT.SubexpDensePolynomial

namespace OAI.Algorithms

/-!
# Executable represented jet reconstruction

Every polynomial is a dense coefficient list. The executable definitions take
only a `RingProgram`; the decoder appears in refinement theorems. Counters sum
the actual coefficient-callback counters. Machine/list overhead is separate.
-/

namespace SubexponentialSAT.SubexpCRTExecution

open SubexpDensePolynomial
open scoped BigOperators

section Programs

variable {C : Type*} (ops : SubexpSymbolicCost.RingProgram C)

def geometricProgram (z : List C) : ℕ → (List C × List C) × ℕ
  | 0 => (([ops.oneRun.1], []), ops.oneRun.2)
  | n + 1 =>
      let previous := geometricProgram z n
      let p := mulProgram ops previous.1.1 z
      let s := addProgram ops previous.1.2 previous.1.1
      ((p.1, s.1), previous.2 + p.2 + s.2)

def localInverseProgram (P : List C) (a : C) (D : ℕ) : List C × ℕ :=
  let neg := ops.negRun a
  let scaled := scaleProgram ops neg.1 P
  let one := ops.oneRun
  let z := addProgram ops [one.1] scaled.1
  let geometric := geometricProgram ops z.1 D
  let result := scaleProgram ops a geometric.1.2
  (result.1.take D, neg.2 + scaled.2 + one.2 + z.2 + geometric.2 + result.2)

def correctionProgram (P J : List C) (a : C) (D : ℕ) : List C × ℕ :=
  let inv := localInverseProgram ops P a D
  let result := mulProgram ops J inv.1
  (result.1.take D, inv.2 + result.2)

def factorsProgram {I : Type*} [DecidableEq I] (θ : I → C) (D : ℕ)
    (i : I) : List I → List (List C) × ℕ
  | [] => ([], 0)
  | j :: js =>
      let rest := factorsProgram θ D i js
      if j = i then rest else
        let neg := ops.negRun (θ j)
        let one := ops.oneRun
        (List.replicate D [neg.1, one.1] ++ rest.1, rest.2 + neg.2 + one.2)

def cofactorProgram {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (i : Fin Q) : List C × ℕ :=
  let factors := factorsProgram ops θ D i (List.ofFn id)
  let product := productProgram ops factors.1
  (product.1, factors.2 + product.2)

def termProgram {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (a : Fin Q → C)
    (J : Fin Q → List C) (i : Fin Q) : List C × ℕ :=
  let cofactor := cofactorProgram ops θ D i
  let shifted := shiftProgram ops (θ i) cofactor.1
  let corrected := correctionProgram ops shifted.1 (J i) (a i) D
  let negNode := ops.negRun (θ i)
  let unshifted := shiftProgram ops negNode.1 corrected.1
  let result := mulProgram ops cofactor.1 unshifted.1
  (result.1, cofactor.2 + shifted.2 + corrected.2 + negNode.2 + unshifted.2 + result.2)

def crtProgram {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (a : Fin Q → C)
    (J : Fin Q → List C) : List C × ℕ :=
  let terms := List.ofFn (fun i => termProgram ops θ D a J i)
  let result := sumProgram ops (terms.map Prod.fst)
  (result.1, (terms.map Prod.snd).sum + result.2)

def scalarProductProgram : List C → C × ℕ
  | [] => ops.oneRun
  | a :: as =>
      let rest := scalarProductProgram as
      let result := ops.mulRun a rest.1
      (result.1, rest.2 + result.2)

def constantInverseProgram {Q : ℕ} (δinv : Fin Q → Fin Q → C)
    (D : ℕ) (i : Fin Q) : C × ℕ :=
  let powers := List.ofFn (fun j => if j = i then ops.oneRun
    else SubexpResidueInverse.powerProgram ops (δinv i j) D)
  let product := scalarProductProgram ops (powers.map Prod.fst)
  (product.1, (powers.map Prod.snd).sum + product.2)

def fromDifferencesProgram {Q : ℕ} (θ : Fin Q → C) (D : ℕ)
    (δinv : Fin Q → Fin Q → C) (J : Fin Q → List C) : List C × ℕ :=
  let table := List.Vector.ofFn (fun i => constantInverseProgram ops δinv D i)
  let result := crtProgram ops θ D (fun i => (table.get i).1) J
  (result.1, (table.toList.map Prod.snd).sum + result.2)

/-- Complete reconstruction, including all inverse-table preprocessing. -/
def completeProgram {Q : ℕ} (θ : Fin Q → C) (q μ D : ℕ)
    (J : Fin Q → List C) : List C × ℕ :=
  let table := SubexpResidueInverse.inverseTableProgram ops θ q μ
  let result := fromDifferencesProgram ops θ D (fun i j => (table.1.get i).get j) J
  (result.1, table.2 + result.2)

end Programs

section Refinement

variable {C A : Type*} [CommRing A] (ops : SubexpSymbolicCost.RepresentedRing C A)

theorem geometricProgram_value (z : List C) (D : ℕ) :
    decodeList ops (geometricProgram ops.program z D).1.1 =
      (TruncatedInverse.denseGeometricWithCost (decodeList ops z) D).1.1 ∧
    decodeList ops (geometricProgram ops.program z D).1.2 =
      (TruncatedInverse.denseGeometricWithCost (decodeList ops z) D).1.2 := by
  induction D with
  | zero =>
      simp [geometricProgram, decodeList,
        ops.one_correct, TruncatedInverse.denseGeometricWithCost,
        TruncatedInverse.geometricLoopWithCost]
  | succ D ih =>
      constructor
      · change decodeList ops (mulProgram ops.program _ z).1 = _
        rw [mulProgram_run, mulRun_correct, ih.1]
        rfl
      · change decodeList ops (addProgram ops.program _ _).1 = _
        rw [addProgram_run, addRun_correct, ih.2, ih.1]
        rfl

theorem localInverseProgram_value (P : List C) (a : C) (D : ℕ) :
    decodeList ops (localInverseProgram ops.program P a D).1 =
      (TruncatedInverse.denseInverseWithCost (decodeList ops P) (ops.decode a) D).1 := by
  simp only [localInverseProgram, decodeList, List.map_take]
  change (decodeList ops (scaleProgram ops.program a _).1).take D = _
  rw [scaleProgram_run, scaleRun_correct, (geometricProgram_value ops _ D).2]
  rw [addProgram_run, addRun_correct, scaleProgram_run, scaleRun_correct]
  simp only [ ops.neg_correct, ops.one_correct,
    decodeList, List.map_cons, List.map_nil]
  simp only [TruncatedInverse.denseInverseWithCost, neg_one_mul,
    PolynomialAlgorithm.truncate, PolynomialAlgorithm.add, PolynomialAlgorithm.scale]

theorem correctionProgram_value (P J : List C) (a : C) (D : ℕ) :
    decodeList ops (correctionProgram ops.program P J a D).1 =
      (TruncatedInverse.denseCorrectionWithCost (decodeList ops P)
        (decodeList ops J) (ops.decode a) D).1 := by
  simp only [correctionProgram, decodeList, List.map_take]
  change (decodeList ops (mulProgram ops.program J _).1).take D = _
  rw [mulProgram_run, mulRun_correct, localInverseProgram_value]
  rfl

theorem factorsProgram_value {I : Type*} [DecidableEq I]
    (θ : I → C) (D : ℕ) (i : I) (js : List I) :
    ((factorsProgram ops.program θ D i js).1.map (decodeList ops)) =
      (TruncatedInverse.denseFactorsWithCost (fun j => ops.decode (θ j)) D i js).1 := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      by_cases h : j = i
      · simpa [factorsProgram, TruncatedInverse.denseFactorsWithCost, h] using ih
      · simp [factorsProgram, TruncatedInverse.denseFactorsWithCost, h, ih,
          decodeList, SubexpSymbolicCost.RepresentedRing.program,
          ops.neg_correct, ops.one_correct]

theorem cofactorProgram_value {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (i : Fin Q) :
    decodeList ops (cofactorProgram ops.program θ D i).1 =
      (TruncatedInverse.denseCofactorWithCost (fun j => ops.decode (θ j)) D i).1 := by
  change decodeList ops (productProgram ops.program _).1 = _
  rw [productProgram_run, productRun_correct, factorsProgram_value]
  rfl

theorem termProgram_value {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (a : Fin Q → C)
    (J : Fin Q → List C) (i : Fin Q) :
    decodeList ops (termProgram ops.program θ D a J i).1 =
      (TruncatedInverse.denseTermWithCost (fun j => ops.decode (θ j)) D
        (fun j => ops.decode (a j)) (fun j => decodeList ops (J j)) i).1 := by
  change decodeList ops (mulProgram ops.program _ _).1 = _
  rw [mulProgram_run, mulRun_correct, cofactorProgram_value,
    shiftProgram_run, shiftRun_correct, correctionProgram_value,
    shiftProgram_run, shiftRun_correct, cofactorProgram_value]
  simp only [ ops.neg_correct]
  simp only [TruncatedInverse.denseTermWithCost, neg_one_mul,
    PolynomialAlgorithm.mul, PolynomialAlgorithm.shift]

theorem crtProgram_value {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (a : Fin Q → C)
    (J : Fin Q → List C) :
    decodeList ops (crtProgram ops.program θ D a J).1 =
      (TruncatedInverse.denseCRTWithCost (fun j => ops.decode (θ j)) D
        (fun j => ops.decode (a j)) (fun j => decodeList ops (J j))).1 := by
  change decodeList ops (sumProgram ops.program _).1 = _
  rw [sumProgram_run, sumRun_correct]
  simp only [ List.map_ofFn, Function.comp_def, termProgram_value]
  simp only [TruncatedInverse.denseCRTWithCost, PolynomialAlgorithm.sum,
    List.map_ofFn, Function.comp_def]

theorem scalarProductProgram_value (as : List C) :
    ops.decode (scalarProductProgram ops.program as).1 = (as.map ops.decode).prod := by
  induction as with
  | nil => exact ops.one_correct
  | cons a as ih =>
      change ops.decode (ops.mulRun a _).1 = _
      rw [ops.mul_correct, ih]
      rfl

theorem constantInverseProgram_value {Q : ℕ} (δinv : Fin Q → Fin Q → C)
    (D : ℕ) (i : Fin Q) :
    ops.decode (constantInverseProgram ops.program δinv D i).1 =
      TruncatedInverse.constantInverse D (fun j k => ops.decode (δinv j k)) i := by
  simp only [constantInverseProgram, scalarProductProgram_value, List.map_ofFn, Function.comp_def, List.prod_ofFn]
  simp only [apply_ite Prod.fst, apply_ite ops.decode, ops.one_correct,
    SubexpResidueInverse.powerProgram_run, SubexpResidueInverse.powerRun_value]
  rw [← Finset.prod_erase (a := i)
    (f := fun j => if j = i then 1 else ops.decode (δinv i j) ^ D) Finset.univ (by simp)]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

theorem fromDifferencesProgram_value {Q : ℕ} (θ : Fin Q → C) (D : ℕ)
    (δinv : Fin Q → Fin Q → C) (J : Fin Q → List C) :
    decodeList ops (fromDifferencesProgram ops.program θ D δinv J).1 =
      (SubexpPolynomialCost.crtFromDifferences (fun j => ops.decode (θ j)) D
        (fun i j => ops.decode (δinv i j)) (fun j => decodeList ops (J j))).1 := by
  change decodeList ops (crtProgram ops.program θ D _ J).1 = _
  rw [crtProgram_value, SubexpPolynomialCost.crtFromDifferences_value]
  simp only [List.Vector.get_ofFn, constantInverseProgram_value]

theorem completeProgram_value {Q : ℕ} (θ : Fin Q → C) (q μ D : ℕ)
    (J : Fin Q → List C) :
    decodeList ops (completeProgram ops.program θ q μ D J).1 =
      (SubexpResidueInverse.crtFromResiduesWithCost (fun j => ops.decode (θ j)) q μ D
        (fun j => decodeList ops (J j))).1 := by
  change decodeList ops (fromDifferencesProgram ops.program θ D _ J).1 = _
  rw [fromDifferencesProgram_value]
  simp only [SubexpResidueInverse.inverseTableProgram_run,
    SubexpResidueInverse.inverseTableRun_value]
  rfl

theorem completeProgram_correct {E : Type*} [Field E] [Fintype E]
    {Q : ℕ} [NeZero Q] (θ : Fin Q → C) (ρ : A →+* E) (q : ℕ)
    (hq : Fintype.card E = q) (π : A) (μ : ℕ) (hπ : π ^ μ = 0)
    (hker : ∀ x, ρ x = 0 → π ∣ x)
    (hθ : Function.Injective (fun i => ρ (ops.decode (θ i))))
    (D : ℕ) (hD : 0 < D) (J : Fin Q → List C) (H : Polynomial A)
    (hH : H.natDegree < Q * D)
    (hjets : ∀ i, Truncation.trunc D (PolynomialAlgorithm.denote (decodeList ops (J i))) =
      JetCRT.jet (ops.decode (θ i)) D H)
    (hlength : ∀ i, (J i).length ≤ D) :
    PolynomialAlgorithm.denote (decodeList ops (completeProgram ops.program θ q μ D J).1) = H := by
  rw [completeProgram_value]
  exact SubexpResidueInverse.crtFromResiduesWithCost_correct _ ρ q hq π μ hπ hker hθ
    D hD _ H hH hjets (by simpa using hlength)

/-- The first output coefficient, with a zero default for an empty list,
has the expected constant-coefficient semantics. -/
theorem head_decode_of_denote_eq (P : List C) (H : Polynomial A)
    (h : PolynomialAlgorithm.denote (decodeList ops P) = H) :
    ops.decode (P.headD ops.zeroRun.1) = H.coeff 0 := by
  rw [← h]
  cases P with
  | nil => simp [decodeList, ops.zero_correct]
  | cons a P => simp [decodeList, PolynomialAlgorithm.coeff_denote ]

end Refinement

def geometricBudget (D L : ℕ) : ℕ := 1 + D * (1 + D * L) * (2 * L + 2)
def localBudget (D L : ℕ) : ℕ := L + 4 + geometricBudget D L + D * L
def cofactorBudget (Q D : ℕ) : ℕ :=
  2 * Q + 1 + 6 * (Q * D) * (1 + 2 * (Q * D))
def termBudget (Q D : ℕ) : ℕ :=
  let L := TruncatedInverse.cofactorLength Q D
  cofactorBudget Q D + 4 * L ^ 2 + localBudget D (2 * L) +
    2 * D ^ 2 + D + 1 + 4 * D ^ 2 + 4 * L * D + L
def crtBudget (Q D : ℕ) : ℕ :=
  Q * (termBudget Q D + TruncatedInverse.termLength Q D)
def fromDifferencesBudget (Q D : ℕ) : ℕ := Q * (Q * (D + 2) + 1) + crtBudget Q D

section Bounds

variable {C A : Type*} [CommRing A] (ops : SubexpSymbolicCost.RepresentedRing C A)

theorem geometricProgram_length (z : List C) (D : ℕ) :
    (geometricProgram ops.program z D).1.1.length ≤ 1 + D * z.length ∧
    (geometricProgram ops.program z D).1.2.length ≤ 1 + D * z.length := by
  have h := TruncatedInverse.denseGeometric_length (decodeList ops z) D
  rw [← (geometricProgram_value ops z D).1, ← (geometricProgram_value ops z D).2] at h
  simpa only [decodeList_length] using h

theorem localInverseProgram_length (P : List C) (a : C) (D : ℕ) :
    (localInverseProgram ops.program P a D).1.length ≤ D := by
  simp only [localInverseProgram, List.length_take]
  exact Nat.min_le_left _ _

theorem correctionProgram_length (P J : List C) (a : C) (D : ℕ) :
    (correctionProgram ops.program P J a D).1.length ≤ D := by
  simp only [correctionProgram, List.length_take]
  exact Nat.min_le_left _ _

theorem factorsProgram_length {I : Type*} [DecidableEq I] (θ : I → C)
    (D : ℕ) (i : I) (js : List I) :
    (factorsProgram ops.program θ D i js).1.length ≤ js.length * D := by
  have h := TruncatedInverse.denseFactors_length (fun j => ops.decode (θ j)) D i js
  rw [← factorsProgram_value ops θ D i js, List.length_map] at h
  exact h

theorem factorsProgram_each_length {I : Type*} [DecidableEq I] (θ : I → C)
    (D : ℕ) (i : I) (js : List I) :
    ∀ P ∈ (factorsProgram ops.program θ D i js).1, P.length ≤ 2 := by
  intro P hP
  have hm : decodeList ops P ∈
      (TruncatedInverse.denseFactorsWithCost (fun j => ops.decode (θ j)) D i js).1 := by
    rw [← factorsProgram_value]
    exact List.mem_map.mpr ⟨P, hP, rfl⟩
  simpa only [decodeList_length] using
    TruncatedInverse.denseFactors_each_length (fun j => ops.decode (θ j)) D i js _ hm

theorem cofactorProgram_length {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (i : Fin Q) :
    (cofactorProgram ops.program θ D i).1.length ≤ TruncatedInverse.cofactorLength Q D := by
  rw [← decodeList_length ops, cofactorProgram_value]
  exact TruncatedInverse.denseCofactor_length _ D i

theorem termProgram_length {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (a : Fin Q → C)
    (J : Fin Q → List C) (i : Fin Q) :
    (termProgram ops.program θ D a J i).1.length ≤ TruncatedInverse.termLength Q D := by
  rw [← decodeList_length ops, termProgram_value]
  exact TruncatedInverse.denseTerm_length _ D _ _ i

theorem completeProgram_length {Q : ℕ} (θ : Fin Q → C) (q μ D : ℕ)
    (J : Fin Q → List C) :
    (completeProgram ops.program θ q μ D J).1.length ≤ 4 * (Q + 1) * (D + 1) := by
  rw [← decodeList_length ops, completeProgram_value]
  exact SubexpResidueInverse.crtFromResiduesWithCost_length _ q μ D _

variable {B : ℕ} (budget : SubexpSymbolicCost.ScalarBudget ops B)
include budget

theorem geometricProgram_cost (z : List C) (D : ℕ) :
    (geometricProgram ops.program z D).2 ≤ geometricBudget D z.length * B := by
  induction D with
  | zero => simpa [geometricProgram, geometricBudget] using budget.one
  | succ D ih =>
      have hp := (geometricProgram_length ops z D).1
      have hs := (geometricProgram_length ops z D).2
      have hm := mulRun_cost ops budget (geometricProgram ops.program z D).1.1 z
      have ha := (addRun_cost ops budget (geometricProgram ops.program z D).1.2
        (geometricProgram ops.program z D).1.1).trans
        (Nat.mul_le_mul_right B (Nat.min_le_left _ _))
      have hm' : (mulProgram ops.program (geometricProgram ops.program z D).1.1 z).2 ≤
          ((1 + D * z.length) * (2 * z.length + 1)) * B := by
        rw [mulProgram_run]
        apply hm.trans
        calc
          _ ≤ (2 * (1 + D * z.length) * z.length + (1 + D * z.length)) * B := by gcongr
          _ = _ := by ring
      have ha' : (addProgram ops.program (geometricProgram ops.program z D).1.2
          (geometricProgram ops.program z D).1.1).2 ≤ (1 + D * z.length) * B := by
        rw [addProgram_run]
        exact ha.trans (Nat.mul_le_mul_right B hs)
      change (geometricProgram ops.program z D).2 + _ + _ ≤ _
      calc
        _ ≤ geometricBudget D z.length * B +
            ((1 + D * z.length) * (2 * z.length + 1)) * B +
            (1 + D * z.length) * B := Nat.add_le_add (Nat.add_le_add ih hm') ha'
        _ = (1 + (D + 1) * (1 + D * z.length) * (2 * z.length + 2)) * B := by
          unfold geometricBudget
          ring
        _ ≤ geometricBudget (D + 1) z.length * B := by
          unfold geometricBudget
          gcongr
          omega

theorem localInverseProgram_cost (P : List C) (a : C) (D L : ℕ)
    (hL : 1 ≤ L) (hP : P.length ≤ L) :
    (localInverseProgram ops.program P a D).2 ≤ localBudget D L * B := by
  let scaled := scaleProgram ops.program (ops.negRun a).1 P
  let z := addProgram ops.program [ops.oneRun.1] scaled.1
  let g := geometricProgram ops.program z.1 D
  have hz : z.1.length ≤ L := by
    simp only [z, addProgram_run, addRun_length, List.length_singleton,
      scaled, scaleProgram_run, scaleRun_length]
    exact max_le hL hP
  have hn := budget.neg a
  have ho := budget.one
  have hscale : scaled.2 ≤ L * B := by
    dsimp only [scaled]
    rw [scaleProgram_run]
    exact (scaleRun_cost ops budget _ P).trans (Nat.mul_le_mul_right B hP)
  have hadd : z.2 ≤ B := by
    have h := (addRun_cost ops budget [ops.oneRun.1] scaled.1).trans
      (Nat.mul_le_mul_right B (Nat.min_le_left _ _))
    simpa [z] using h
  have hg : g.2 ≤ geometricBudget D L * B := by
    apply (geometricProgram_cost ops budget z.1 D).trans
    unfold geometricBudget
    gcongr
  have hlen : g.1.2.length ≤ 1 + D * L :=
    (geometricProgram_length ops z.1 D).2.trans (by gcongr)
  have hout : (scaleProgram ops.program a g.1.2).2 ≤ (1 + D * L) * B := by
    rw [scaleProgram_run]
    exact (scaleRun_cost ops budget a _).trans (Nat.mul_le_mul_right B hlen)
  change (ops.negRun a).2 + scaled.2 + ops.oneRun.2 + z.2 + g.2 +
    (scaleProgram ops.program a g.1.2).2 ≤ _
  calc
    _ ≤ B + L * B + B + B + geometricBudget D L * B + (1 + D * L) * B := by omega
    _ = localBudget D L * B := by unfold localBudget; ring

theorem correctionProgram_cost (P J : List C) (a : C) (D L : ℕ)
    (hL : 1 ≤ L) (hP : P.length ≤ L) (hJ : J.length ≤ D) :
    (correctionProgram ops.program P J a D).2 ≤ (localBudget D L + 2 * D ^ 2 + D) * B := by
  have hi := localInverseProgram_cost ops budget P a D L hL hP
  have hl := localInverseProgram_length ops P a D
  have hm := mulRun_cost ops budget J (localInverseProgram ops.program P a D).1
  have hm' : (mulProgram ops.program J (localInverseProgram ops.program P a D).1).2 ≤
      (2 * D ^ 2 + D) * B := by
    rw [mulProgram_run]
    apply hm.trans
    calc
      _ ≤ (2 * D * D + D) * B := by gcongr
      _ = _ := by ring
  change _ + _ ≤ _
  calc
    _ ≤ localBudget D L * B + (2 * D ^ 2 + D) * B := Nat.add_le_add hi hm'
    _ = _ := by ring

theorem factorsProgram_cost {I : Type*} [DecidableEq I] (θ : I → C)
    (D : ℕ) (i : I) (js : List I) :
    (factorsProgram ops.program θ D i js).2 ≤ 2 * js.length * B := by
  induction js with
  | nil => simp [factorsProgram]
  | cons j js ih =>
      have hn := budget.neg (θ j)
      have ho := budget.one
      by_cases h : j = i
      · simp only [factorsProgram, h, ↓reduceIte, List.length_cons]
        exact ih.trans (by gcongr; omega)
      · simp only [factorsProgram, ite_eq_right h]
        change (factorsProgram ops.program θ D i js).2 + (ops.negRun (θ j)).2 + ops.oneRun.2 ≤ _
        calc
          _ ≤ 2 * js.length * B + B + B := Nat.add_le_add (Nat.add_le_add ih hn) ho
          _ = _ := by simp only [List.length_cons]; ring

theorem cofactorProgram_cost {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (i : Fin Q) :
    (cofactorProgram ops.program θ D i).2 ≤ cofactorBudget Q D * B := by
  let fs := factorsProgram ops.program θ D i (List.ofFn id)
  have hf : fs.2 ≤ 2 * Q * B := by
    simpa [fs] using factorsProgram_cost ops budget θ D i (List.ofFn id)
  have hl : fs.1.length ≤ Q * D := by
    simpa [fs] using factorsProgram_length ops θ D i (List.ofFn id)
  have hp := productRun_cost ops budget fs.1 2
    (factorsProgram_each_length ops θ D i (List.ofFn id))
  have hp' : (productProgram ops.program fs.1).2 ≤
      (1 + 6 * (Q * D) * (1 + 2 * (Q * D))) * B := by
    rw [productProgram_run]
    apply hp.trans
    calc
      _ ≤ (1 + 3 * (Q * D) * 2 * (1 + (Q * D) * 2)) * B := by gcongr
      _ = _ := by ring
  change fs.2 + (productProgram ops.program fs.1).2 ≤ _
  calc
    _ ≤ 2 * Q * B + (1 + 6 * (Q * D) * (1 + 2 * (Q * D))) * B := Nat.add_le_add hf hp'
    _ = _ := by unfold cofactorBudget; ring

theorem termProgram_cost {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (a : Fin Q → C)
    (J : Fin Q → List C) (hJ : ∀ i, (J i).length ≤ D) (i : Fin Q) :
    (termProgram ops.program θ D a J i).2 ≤ termBudget Q D * B := by
  let L := TruncatedInverse.cofactorLength Q D
  let cofactor := cofactorProgram ops.program θ D i
  let shifted := shiftProgram ops.program (θ i) cofactor.1
  let corrected := correctionProgram ops.program shifted.1 (J i) (a i) D
  let negNode := ops.negRun (θ i)
  let unshifted := shiftProgram ops.program negNode.1 corrected.1
  have hl : cofactor.1.length ≤ L := cofactorProgram_length ops θ D i
  have hsl : shifted.1.length ≤ 2 * L := by
    dsimp only [shifted]
    rw [shiftProgram_run]
    exact (shiftRun_length ops (θ i) cofactor.1).trans (Nat.mul_le_mul_left 2 hl)
  have hcl : corrected.1.length ≤ D := correctionProgram_length ops _ _ _ D
  have hul : unshifted.1.length ≤ 2 * D := by
    dsimp only [unshifted]
    rw [shiftProgram_run]
    exact (shiftRun_length ops negNode.1 corrected.1).trans (Nat.mul_le_mul_left 2 hcl)
  have hc : cofactor.2 ≤ cofactorBudget Q D * B := cofactorProgram_cost ops budget θ D i
  have hs : shifted.2 ≤ 4 * L ^ 2 * B := by
    dsimp only [shifted]
    rw [shiftProgram_run]
    exact (shiftRun_cost ops budget (θ i) cofactor.1).trans (by gcongr)
  have hcorrect : corrected.2 ≤ (localBudget D (2 * L) + 2 * D ^ 2 + D) * B := by
    apply correctionProgram_cost ops budget _ _ _ D (2 * L) _ hsl (hJ i)
    dsimp [L, TruncatedInverse.cofactorLength]
    omega
  have hn : negNode.2 ≤ B := budget.neg _
  have hu : unshifted.2 ≤ 4 * D ^ 2 * B := by
    dsimp only [unshifted]
    rw [shiftProgram_run]
    exact (shiftRun_cost ops budget negNode.1 corrected.1).trans (by gcongr)
  have hm : (mulProgram ops.program cofactor.1 unshifted.1).2 ≤ (4 * L * D + L) * B := by
    rw [mulProgram_run]
    apply (mulRun_cost ops budget cofactor.1 unshifted.1).trans
    calc
      _ ≤ (2 * L * (2 * D) + L) * B := by gcongr
      _ = _ := by ring
  change cofactor.2 + shifted.2 + corrected.2 + negNode.2 + unshifted.2 +
    (mulProgram ops.program cofactor.1 unshifted.1).2 ≤ _
  calc
    _ ≤ cofactorBudget Q D * B + 4 * L ^ 2 * B +
        (localBudget D (2 * L) + 2 * D ^ 2 + D) * B + B + 4 * D ^ 2 * B +
        (4 * L * D + L) * B := by omega
    _ = termBudget Q D * B := by dsimp [termBudget, L]; ring

theorem crtProgram_cost {Q : ℕ} (θ : Fin Q → C) (D : ℕ) (a : Fin Q → C)
    (J : Fin Q → List C) (hJ : ∀ i, (J i).length ≤ D) :
    (crtProgram ops.program θ D a J).2 ≤ crtBudget Q D * B := by
  let terms := List.ofFn (fun i => termProgram ops.program θ D a J i)
  have hs : (terms.map Prod.snd).sum ≤ Q * (termBudget Q D * B) := by
    simp only [terms, List.map_ofFn, Function.comp_def, List.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin Q, termBudget Q D * B :=
        Finset.sum_le_sum (fun i _ => termProgram_cost ops budget θ D a J hJ i)
      _ = _ := by simp
  have hl : ∀ P ∈ terms.map Prod.fst, P.length ≤ TruncatedInverse.termLength Q D := by
    intro P hP
    simp only [terms, List.map_ofFn, Function.comp_def, List.mem_ofFn] at hP
    obtain ⟨i, rfl⟩ := hP
    exact termProgram_length ops θ D a J i
  have ha : (sumProgram ops.program (terms.map Prod.fst)).2 ≤
      Q * TruncatedInverse.termLength Q D * B := by
    simpa [terms] using sumRun_cost ops budget (terms.map Prod.fst) _ hl
  change (terms.map Prod.snd).sum + (sumProgram ops.program (terms.map Prod.fst)).2 ≤ _
  calc
    _ ≤ Q * (termBudget Q D * B) + Q * TruncatedInverse.termLength Q D * B := Nat.add_le_add hs ha
    _ = _ := by unfold crtBudget; ring

theorem scalarProductProgram_cost (as : List C) :
    (scalarProductProgram ops.program as).2 ≤ (as.length + 1) * B := by
  induction as with
  | nil => simpa [scalarProductProgram] using budget.one
  | cons a as ih =>
      have hm := budget.mul a (scalarProductProgram ops.program as).1
      change (scalarProductProgram ops.program as).2 +
        (ops.mulRun a (scalarProductProgram ops.program as).1).2 ≤ _
      calc
        _ ≤ (as.length + 1) * B + B := Nat.add_le_add ih hm
        _ = _ := by simp only [List.length_cons]; ring

theorem constantInverseProgram_cost {Q : ℕ} (δinv : Fin Q → Fin Q → C)
    (D : ℕ) (i : Fin Q) :
    (constantInverseProgram ops.program δinv D i).2 ≤ (Q * (D + 2) + 1) * B := by
  let powers := List.ofFn (fun j => if j = i then ops.program.oneRun
    else SubexpResidueInverse.powerProgram ops.program (δinv i j) D)
  have heach (j : Fin Q) :
      (if j = i then ops.program.oneRun else
        SubexpResidueInverse.powerProgram ops.program (δinv i j) D).2 ≤ (D + 1) * B := by
    split
    · exact budget.one.trans (by simpa using Nat.mul_le_mul_right B (show 1 ≤ D + 1 by omega))
    · simpa only [SubexpResidueInverse.powerProgram_run] using
        SubexpResidueInverse.powerRun_cost ops budget (δinv i j) D
  have hs : (powers.map Prod.snd).sum ≤ Q * ((D + 1) * B) := by
    simp only [powers, List.map_ofFn, Function.comp_def, List.sum_ofFn]
    calc
      _ ≤ ∑ _j : Fin Q, (D + 1) * B := Finset.sum_le_sum (fun j _ => heach j)
      _ = _ := by simp
  have hp : (scalarProductProgram ops.program (powers.map Prod.fst)).2 ≤ (Q + 1) * B := by
    simpa [powers] using scalarProductProgram_cost ops budget (powers.map Prod.fst)
  change (powers.map Prod.snd).sum + (scalarProductProgram ops.program (powers.map Prod.fst)).2 ≤ _
  calc
    _ ≤ Q * ((D + 1) * B) + (Q + 1) * B := Nat.add_le_add hs hp
    _ = _ := by ring

theorem fromDifferencesProgram_cost {Q : ℕ} (θ : Fin Q → C) (D : ℕ)
    (δinv : Fin Q → Fin Q → C) (J : Fin Q → List C) (hJ : ∀ i, (J i).length ≤ D) :
    (fromDifferencesProgram ops.program θ D δinv J).2 ≤ fromDifferencesBudget Q D * B := by
  have hs : (∑ i : Fin Q, (constantInverseProgram ops.program δinv D i).2) ≤
      Q * ((Q * (D + 2) + 1) * B) := by
    calc
      _ ≤ ∑ _i : Fin Q, (Q * (D + 2) + 1) * B :=
        Finset.sum_le_sum (fun i _ => constantInverseProgram_cost ops budget δinv D i)
      _ = _ := by simp
  simp only [fromDifferencesProgram, List.Vector.toList_ofFn, List.map_ofFn,
    Function.comp_def, List.sum_ofFn]
  apply (Nat.add_le_add hs (crtProgram_cost ops budget θ D _ J hJ)).trans
  exact le_of_eq (by unfold fromDifferencesBudget; ring)

theorem completeProgram_cost {Q : ℕ} (θ : Fin Q → C) (q μ D : ℕ)
    (J : Fin Q → List C) (hJ : ∀ i, (J i).length ≤ D) :
    (completeProgram ops.program θ q μ D J).2 ≤
      (Q ^ 2 * (q + 2 * μ + 9) + fromDifferencesBudget Q D) * B := by
  unfold completeProgram
  rw [SubexpResidueInverse.inverseTableProgram_run]
  apply (Nat.add_le_add (SubexpResidueInverse.inverseTableRun_cost ops budget θ q μ)
    (fromDifferencesProgram_cost ops budget θ D _ J hJ)).trans
  exact le_of_eq (by ring)

end Bounds

theorem fromDifferencesBudget_uniform (Q D : ℕ) :
    fromDifferencesBudget Q D ≤ 256 * (Q + 1) ^ 3 * (D + 1) ^ 4 := by
  dsimp [fromDifferencesBudget, crtBudget, termBudget, cofactorBudget, localBudget,
    geometricBudget, TruncatedInverse.cofactorLength, TruncatedInverse.termLength]
  ring_nf
  omega

theorem completeProgram_uniform {C A : Type*} [CommRing A]
    (ops : SubexpSymbolicCost.RepresentedRing C A) {B : ℕ}
    (budget : SubexpSymbolicCost.ScalarBudget ops B) {Q : ℕ}
    (θ : Fin Q → C) (q μ D : ℕ) (J : Fin Q → List C) (hJ : ∀ i, (J i).length ≤ D) :
    (completeProgram ops.program θ q μ D J).2 ≤
      (Q ^ 2 * (q + 2 * μ + 9) + 256 * (Q + 1) ^ 3 * (D + 1) ^ 4) * B := by
  apply (completeProgram_cost ops budget θ q μ D J hJ).trans
  exact Nat.mul_le_mul_right B (Nat.add_le_add_left (fromDifferencesBudget_uniform Q D) _)

theorem completeProgram_fullNodeCost {C A : Type*} [CommRing A]
    (ops : SubexpSymbolicCost.RepresentedRing C A) {B : ℕ}
    (budget : SubexpSymbolicCost.ScalarBudget ops B) {Q : ℕ}
    (θ : Fin Q → C) (D : ℕ) (J : Fin Q → List C) (hJ : ∀ i, (J i).length ≤ D) :
    (completeProgram ops.program θ (Q + 1) (D + 1) D J).2 ≤
      512 * (Q + 1) ^ 3 * (D + 1) ^ 4 * B := by
  apply (completeProgram_uniform ops budget θ (Q + 1) (D + 1) D J hJ).trans
  apply Nat.mul_le_mul_right B
  ring_nf
  omega

section PreparedQuartic

open SubexpSymbolicCost SubexpQuarticRing

/-- This decoder is used only in specifications. The CRT program receives
the binary callback record and never evaluates the semantic quotient map. -/
noncomputable def selectedDecoder (p D : ℕ) [Fact p.Prime] (x : QuarticCode p D) :
    SubexpActualRing.Ring p (D + 1) :=
  quotientDenote (QuarticSearch.liftedCoefficients p (D + 1))
    (x.map (wordValue p (D + 1)))

theorem preparedComplete_spec (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1)) (t z o : QuarticCode p D)
    (ht : t.map (wordValue p (D + 1)) =
      reductionData (QuarticSearch.liftedCoefficients p (D + 1)))
    (hz : selectedDecoder p D z = 0) (ho : selectedDecoder p D o = 1)
    {Q : ℕ} [NeZero Q] (θ : Fin Q → QuarticCode p D)
    (hθ : Function.Injective (fun i =>
      SubexpActualRing.rho p (D + 1) (Nat.zero_lt_succ D) (selectedDecoder p D (θ i))))
    (hD : 0 < D) (J : Fin Q → List (QuarticCode p D))
    (H : Polynomial (SubexpActualRing.Ring p (D + 1))) (hH : H.natDegree < Q * D)
    (hjets : ∀ i, Truncation.trunc D
      (PolynomialAlgorithm.denote ((J i).map (selectedDecoder p D))) =
        JetCRT.jet (selectedDecoder p D (θ i)) D H)
    (hlength : ∀ i, (J i).length ≤ D) :
    PolynomialAlgorithm.denote
        ((completeProgram (preparedProgram p D M t z o) θ (p ^ 4) (D + 1) D J).1.map
          (selectedDecoder p D)) = H ∧
      (completeProgram (preparedProgram p D M t z o) θ (p ^ 4) (D + 1) D J).2 ≤
        (Q ^ 2 * (p ^ 4 + 2 * (D + 1) + 9) + 256 * (Q + 1) ^ 3 * (D + 1) ^ 4) *
          quarticEventBudget D (Nat.log 2 p + 1) := by
  let ops := preparedRing p D M (QuarticSearch.liftedCoefficients p (D + 1)) t z o ht hz ho
  constructor
  · change PolynomialAlgorithm.denote
      (SubexpDensePolynomial.decodeList ops (completeProgram ops.program θ (p ^ 4) (D + 1) D J).1) = H
    exact completeProgram_correct ops θ (SubexpActualRing.rho p (D + 1) (Nat.zero_lt_succ D))
      (p ^ 4) (SubexpActualRing.extension_card p) (p : SubexpActualRing.Ring p (D + 1))
      (D + 1) (SubexpActualRing.prime_power_zero p (D + 1))
      (fun x hx => (SubexpActualRing.rho_eq_zero_iff p (D + 1) (Nat.zero_lt_succ D) x).mp hx)
      hθ D hD J H hH hjets hlength
  · exact completeProgram_uniform ops
      (preparedRing_budget p D M (QuarticSearch.liftedCoefficients p (D + 1)) t z o ht hz ho)
      θ (p ^ 4) (D + 1) D J hlength

end PreparedQuartic

end SubexponentialSAT.SubexpCRTExecution

end OAI.Algorithms
