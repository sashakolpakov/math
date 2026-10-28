import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDensePolynomial
import OAI.Algorithms.SubexponentialSAT.SubexpFactorCode

namespace OAI.Algorithms

/-!
# Executable Taylor and factor preprocessing for coefficient code words

Only RingProgram callbacks occur in runtime definitions. Code words need no
ring laws. Decoding the computed arrays yields the true shifted-polynomial
coefficients. Arithmetic callback costs and list visits are kept separate.
-/

namespace SubexponentialSAT.SubexpTaylorExecution

open scoped BigOperators
open SubexpRowInterpolation (PolynomialCode)

variable {C R : Type*}

def mapCode (decode : C → R) : PolynomialCode C → PolynomialCode R
  | .constant c => .constant (decode c)
  | .indeterminate => .indeterminate
  | .add p q => .add (mapCode decode p) (mapCode decode q)
  | .mul p q => .mul (mapCode decode p) (mapCode decode q)

@[simp] theorem mapCode_weight (decode : C → R) (p : PolynomialCode C) :
    SubexpTaylorCode.codeWeight (mapCode decode p) = SubexpTaylorCode.codeWeight p := by
  induction p <;> simp_all [mapCode, SubexpTaylorCode.codeWeight]

@[simp] theorem mapCode_lengthBound (decode : C → R) (p : PolynomialCode C) :
    SubexpTaylorCode.codeLengthBound (mapCode decode p) = SubexpTaylorCode.codeLengthBound p := by
  induction p <;> simp_all [mapCode, SubexpTaylorCode.codeLengthBound]

def compileCodeProgram (ops : SubexpSymbolicCost.RingProgram C) : PolynomialCode C → List C × ℕ
  | .constant a => ([a], 0)
  | .indeterminate => ([ops.zeroRun.1, ops.oneRun.1], ops.zeroRun.2 + ops.oneRun.2)
  | .add p q =>
      let left := compileCodeProgram ops p
      let right := compileCodeProgram ops q
      let out := SubexpDensePolynomial.addProgram ops left.1 right.1
      (out.1, left.2 + right.2 + out.2)
  | .mul p q =>
      let left := compileCodeProgram ops p
      let right := compileCodeProgram ops q
      let out := SubexpDensePolynomial.mulProgram ops left.1 right.1
      (out.1, left.2 + right.2 + out.2)

def readProgram (zero : C) : List C → ℕ → C × ℕ
  | [], _ => (zero, 1)
  | a :: _, 0 => (a, 1)
  | _ :: P, n + 1 =>
      let rest := readProgram zero P n
      (rest.1, rest.2 + 1)

theorem readProgram_getD (zero : C) (P : List C) (n : ℕ) :
    (readProgram zero P n).1 = P.getD n zero := by
  induction P generalizing n with
  | nil => simp [readProgram]
  | cons a P ih => cases n <;> simp [readProgram, ih ]

theorem readProgram_cost (zero : C) (P : List C) (n : ℕ) :
    (readProgram zero P n).2 ≤ n + 1 := by
  induction P generalizing n with
  | nil => simp [readProgram]
  | cons a P ih =>
      cases n with
      | zero => simp [readProgram]
      | succ n => simpa [readProgram, Nat.add_assoc] using Nat.add_le_add_right (ih n) 1

structure RowCache (C : Type*) where
  values : Array C
  callbackCost : ℕ
  listReads : ℕ

structure TaylorCache (C : Type*) where
  values : Array (Array C)
  callbackCost : ℕ
  listReads : ℕ

structure CompiledTaylorCache (C : Type*) where
  taylor : TaylorCache C
  compileCost : ℕ

def buildRowProgram (ops : SubexpSymbolicCost.RingProgram C) (θ : C) (q : ℕ)
    (P : List C) : RowCache C :=
  let shifted := SubexpDensePolynomial.shiftProgram ops θ P
  let zero := ops.zeroRun
  let entries := Array.ofFn (fun j : Fin (q + 1) => readProgram zero.1 shifted.1 j.val)
  ⟨entries.map Prod.fst, shifted.2 + zero.2, (entries.toList.map Prod.snd).sum⟩

def buildTaylorProgram {D : ℕ} (ops : SubexpSymbolicCost.RingProgram C) (θ : C)
    (q : ℕ) (rows : Fin D → List C) : TaylorCache C :=
  let cached := Array.ofFn (fun i : Fin D => buildRowProgram ops θ q (rows i))
  ⟨cached.map RowCache.values, (cached.toList.map RowCache.callbackCost).sum,
    (cached.toList.map RowCache.listReads).sum⟩

def coefficients {D q : ℕ} (zero : C) (cache : TaylorCache C) : Fin (q + 1) → Fin D → C :=
  fun j i => (cache.values.getD i.val #[]).getD j.val zero

def buildCodeTaylorProgram {D : ℕ} (ops : SubexpSymbolicCost.RingProgram C)
    (θ : C) (q : ℕ) (rows : Fin D → PolynomialCode C) : CompiledTaylorCache C :=
  let compiled := Array.ofFn (fun i : Fin D => compileCodeProgram ops (rows i))
  ⟨buildTaylorProgram ops θ q (fun i : Fin D => (compiled.getD i.val ([], 0)).1),
    (compiled.toList.map Prod.snd).sum⟩

structure FactorResult (D p q r : ℕ) (K C : Type*) where
  data : SubexpProgramBuilder.FactorData D p q r K C
  compileCost : ℕ
  shiftCost : ℕ
  listReads : ℕ

def emptyCache (C : Type*) : CompiledTaylorCache C := ⟨⟨#[], 0, 0⟩, 0⟩

def buildFactorProgram {D p r : ℕ} {K : Type*} (ops : SubexpSymbolicCost.RingProgram C)
    (θ : C) (q : ℕ) (source : SubexpFactorCode.FactorSource D p r K C) :
    FactorResult D p q r K C :=
  let cached := Array.ofFn (fun i : Fin source.arity =>
    buildCodeTaylorProgram ops θ q (source.rows i))
  ⟨{ arity := source.arity
     color := source.color
     origin := source.origin
     taylor := fun i => coefficients ops.zeroRun.1 (cached.getD i.val (emptyCache C)).taylor
     table := source.table },
    (cached.toList.map CompiledTaylorCache.compileCost).sum,
    (cached.toList.map (fun c => c.taylor.callbackCost)).sum,
    (cached.toList.map (fun c => c.taylor.listReads)).sum⟩

structure FactorBatch (D p q r : ℕ) (K C : Type*) where
  data : List (SubexpProgramBuilder.FactorData D p q r K C)
  compileCost : ℕ
  shiftCost : ℕ
  listReads : ℕ

def buildFactorsProgram {D p r : ℕ} {K : Type*} (ops : SubexpSymbolicCost.RingProgram C)
    (θ : C) (q : ℕ) : List (SubexpFactorCode.FactorSource D p r K C) → FactorBatch D p q r K C
  | [] => ⟨[], 0, 0, 0⟩
  | source :: sources =>
      let first := buildFactorProgram ops θ q source
      let rest := buildFactorsProgram ops θ q sources
      ⟨first.data :: rest.data, first.compileCost + rest.compileCost,
        first.shiftCost + rest.shiftCost, first.listReads + rest.listReads⟩

@[simp] theorem buildFactorsProgram_data {D p r : ℕ} {K : Type*}
    (ops : SubexpSymbolicCost.RingProgram C) (θ : C) (q : ℕ)
    (sources : List (SubexpFactorCode.FactorSource D p r K C)) :
    (buildFactorsProgram ops θ q sources).data =
      sources.map (fun source => (buildFactorProgram ops θ q source).data) := by
  induction sources with
  | nil => rfl
  | cons source sources ih => simp only [buildFactorsProgram, List.map_cons, ih]

@[simp] theorem buildRowProgram_size (ops : SubexpSymbolicCost.RingProgram C)
    (θ : C) (q : ℕ) (P : List C) : (buildRowProgram ops θ q P).values.size = q + 1 := by
  simp [buildRowProgram]

@[simp] theorem buildTaylorProgram_size {D : ℕ} (ops : SubexpSymbolicCost.RingProgram C)
    (θ : C) (q : ℕ) (rows : Fin D → List C) :
    (buildTaylorProgram ops θ q rows).values.size = D := by
  simp [buildTaylorProgram]

theorem buildTaylorProgram_slots {D : ℕ} (ops : SubexpSymbolicCost.RingProgram C)
    (θ : C) (q : ℕ) (rows : Fin D → List C) :
    ((buildTaylorProgram ops θ q rows).values.toList.map Array.size).sum = D * (q + 1) := by
  simp [buildTaylorProgram, Array.toList_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]

section Correctness

variable [CommRing R] (ops : SubexpSymbolicCost.RepresentedRing C R)

theorem compileCodeProgram_decode (p : PolynomialCode C) :
    SubexpDensePolynomial.decodeList ops (compileCodeProgram ops.program p).1 =
      (SubexpTaylorCode.compileCodeWithCost (mapCode ops.decode p)).1 := by
  induction p with
  | constant a => rfl
  | indeterminate => simp [compileCodeProgram, SubexpDensePolynomial.decodeList,
      ops.zero_correct, ops.one_correct, mapCode, SubexpTaylorCode.compileCodeWithCost
      ]
  | add p q hp hq =>
      simp only [compileCodeProgram, SubexpDensePolynomial.addProgram_run,
        SubexpDensePolynomial.addRun_correct, hp, hq]
      rfl
  | mul p q hp hq =>
      simp only [compileCodeProgram, SubexpDensePolynomial.mulProgram_run,
        SubexpDensePolynomial.mulRun_correct, hp, hq]
      rfl

theorem compileCodeProgram_denote (p : PolynomialCode C) :
    PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops
      (compileCodeProgram ops.program p).1) = (mapCode ops.decode p).denote := by
  rw [compileCodeProgram_decode, SubexpTaylorCode.denote_compileCodeWithCost]

theorem compileCodeProgram_length (p : PolynomialCode C) :
    (compileCodeProgram ops.program p).1.length ≤ SubexpTaylorCode.codeLengthBound p := by
  rw [← SubexpDensePolynomial.decodeList_length ops, compileCodeProgram_decode]
  simpa using SubexpTaylorCode.compileCode_lengthBound (mapCode ops.decode p)

theorem readProgram_coeff (zero : C) (hz : ops.decode zero = 0) (P : List C) (n : ℕ) :
    ops.decode (readProgram zero P n).1 =
      (PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops P)).coeff n := by
  rw [PolynomialAlgorithm.coeff_denote]
  induction P generalizing n with
  | nil => exact hz
  | cons a P ih => cases n <;> simp [readProgram, PolynomialAlgorithm.coeff,
      SubexpDensePolynomial.decodeList, ih]

theorem buildRowProgram_coeff (θ : C) (q : ℕ) (P : List C) (j : Fin (q + 1)) :
    ops.decode ((buildRowProgram ops.program θ q P).values.getD j.val ops.zeroRun.1) =
      ((PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops P)).comp
        (Polynomial.X + Polynomial.C (ops.decode θ))).coeff j.val := by
  rw [buildRowProgram, SubexpTaylorCode.getD_map_ofFn]
  rw [show ops.program.zeroRun.1 = ops.zeroRun.1 from rfl]
  rw [readProgram_coeff ops _ ops.zero_correct, SubexpDensePolynomial.shiftProgram_run,
    SubexpDensePolynomial.shiftRun_correct, PolynomialAlgorithm.denote_shift]

@[simp] theorem buildTaylorProgram_row {D : ℕ} (θ : C) (q : ℕ)
    (rows : Fin D → List C) (i : Fin D) :
    (buildTaylorProgram ops.program θ q rows).values.getD i.val #[] =
      (buildRowProgram ops.program θ q (rows i)).values := by
  exact SubexpTaylorCode.getD_map_ofFn _ _ i #[]

theorem coefficients_buildTaylorProgram {D : ℕ} (θ : C) (q : ℕ)
    (rows : Fin D → List C) (j : Fin (q + 1)) (i : Fin D) :
    ops.decode (coefficients ops.zeroRun.1 (buildTaylorProgram ops.program θ q rows) j i) =
      ((PolynomialAlgorithm.denote (SubexpDensePolynomial.decodeList ops (rows i))).comp
        (Polynomial.X + Polynomial.C (ops.decode θ))).coeff j.val := by
  unfold coefficients
  rw [buildTaylorProgram_row]
  exact buildRowProgram_coeff ops θ q (rows i) j

@[simp] theorem buildCodeTaylorProgram_taylor {D : ℕ} (θ : C) (q : ℕ)
    (rows : Fin D → PolynomialCode C) :
    (buildCodeTaylorProgram ops.program θ q rows).taylor =
      buildTaylorProgram ops.program θ q (fun i => (compileCodeProgram ops.program (rows i)).1) := by
  simp only [buildCodeTaylorProgram, SubexpTaylorCode.getD_ofFn]

theorem coefficients_buildCodeTaylorProgram {D : ℕ} (θ : C) (q : ℕ)
    (rows : Fin D → PolynomialCode C) (j : Fin (q + 1)) (i : Fin D) :
    ops.decode (coefficients ops.zeroRun.1
      (buildCodeTaylorProgram ops.program θ q rows).taylor j i) =
        (((mapCode ops.decode (rows i)).denote).comp
          (Polynomial.X + Polynomial.C (ops.decode θ))).coeff j.val := by
  rw [buildCodeTaylorProgram_taylor, coefficients_buildTaylorProgram, compileCodeProgram_denote]

/-- The local semantic contract required by the represented factor builder. -/
theorem buildFactorProgram_taylor {D p r : ℕ} {K : Type*} (θ : C) (q : ℕ)
    (source : SubexpFactorCode.FactorSource D p r K C)
    (i : Fin source.arity) (j : Fin (q + 1)) (w : Fin D) :
    ops.decode ((buildFactorProgram ops.program θ q source).data.taylor i j w) =
      (((mapCode ops.decode (source.rows i w)).denote).comp
        (Polynomial.X + Polynomial.C (ops.decode θ))).coeff j.val := by
  simp only [buildFactorProgram, SubexpTaylorCode.getD_ofFn]
  exact coefficients_buildCodeTaylorProgram ops θ q (source.rows i) j w

theorem buildFactorProgram_taylor_eq {D p r : ℕ} {K : Type*} (θ : C) (q : ℕ)
    (source : SubexpFactorCode.FactorSource D p r K C)
    (rows : Fin source.arity → Fin D → Polynomial R)
    (hrows : ∀ i w, (mapCode ops.decode (source.rows i w)).denote = rows i w)
    (i : Fin source.arity) (j : Fin (q + 1)) (w : Fin D) :
    ops.decode ((buildFactorProgram ops.program θ q source).data.taylor i j w) =
      ((rows i w).comp (Polynomial.X + Polynomial.C (ops.decode θ))).coeff j.val := by
  rw [buildFactorProgram_taylor, hrows]

variable {B : ℕ} (budget : SubexpSymbolicCost.ScalarBudget ops B)

include budget

theorem compileCodeProgram_cost (p : PolynomialCode C) :
    (compileCodeProgram ops.program p).2 ≤ 4 * SubexpTaylorCode.codeWeight p ^ 2 * B := by
  induction p with
  | constant a => simp [compileCodeProgram]
  | indeterminate =>
      change ops.zeroRun.2 + ops.oneRun.2 ≤ 4 * 2 ^ 2 * B
      have hz := budget.zero
      have ho := budget.one
      omega
  | add p q hp hq =>
      have hl := (compileCodeProgram_length ops p).trans (SubexpTaylorCode.codeLengthBound_le_weight p)
      have ha := (SubexpDensePolynomial.addRun_cost ops budget
        (compileCodeProgram ops.program p).1 (compileCodeProgram ops.program q).1).trans
        (Nat.mul_le_mul_right B ((Nat.min_le_left _ _).trans hl))
      simp only [compileCodeProgram, SubexpDensePolynomial.addProgram_run, SubexpTaylorCode.codeWeight]
      calc
        _ ≤ (4 * SubexpTaylorCode.codeWeight p ^ 2 + 4 * SubexpTaylorCode.codeWeight q ^ 2 +
            SubexpTaylorCode.codeWeight p) * B := by nlinarith
        _ ≤ _ := Nat.mul_le_mul_right B (by
          nlinarith [Nat.zero_le (SubexpTaylorCode.codeWeight p * SubexpTaylorCode.codeWeight q)])
  | mul p q hp hq =>
      have hl := (compileCodeProgram_length ops p).trans (SubexpTaylorCode.codeLengthBound_le_weight p)
      have hr := (compileCodeProgram_length ops q).trans (SubexpTaylorCode.codeLengthBound_le_weight q)
      have hm := (SubexpDensePolynomial.mulRun_cost ops budget
        (compileCodeProgram ops.program p).1 (compileCodeProgram ops.program q).1).trans
        (Nat.mul_le_mul_right B (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hl) hr) hl))
      simp only [compileCodeProgram, SubexpDensePolynomial.mulProgram_run, SubexpTaylorCode.codeWeight]
      calc
        _ ≤ (4 * SubexpTaylorCode.codeWeight p ^ 2 + 4 * SubexpTaylorCode.codeWeight q ^ 2 +
            2 * SubexpTaylorCode.codeWeight p * SubexpTaylorCode.codeWeight q +
            SubexpTaylorCode.codeWeight p) * B := by nlinarith
        _ ≤ _ := Nat.mul_le_mul_right B (by
          nlinarith [Nat.zero_le (SubexpTaylorCode.codeWeight p * SubexpTaylorCode.codeWeight q)])

theorem buildRowProgram_cost (θ : C) (q : ℕ) (P : List C) :
    (buildRowProgram ops.program θ q P).callbackCost ≤ (4 * P.length ^ 2 + 1) * B := by
  have hs := SubexpDensePolynomial.shiftRun_cost ops budget θ P
  have hz := budget.zero
  simp only [buildRowProgram, SubexpDensePolynomial.shiftProgram_run]
  change _ + ops.zeroRun.2 ≤ _
  nlinarith

omit budget

theorem buildRowProgram_reads (θ : C) (q : ℕ) (P : List C) :
    (buildRowProgram ops.program θ q P).listReads ≤ (q + 1) ^ 2 := by
  simp only [buildRowProgram, Array.toList_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _j : Fin (q + 1), (q + 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact (readProgram_cost _ _ j.val).trans (by omega)
    _ = _ := by simp [pow_two]

include budget

theorem buildTaylorProgram_cost {D : ℕ} (θ : C) (q L : ℕ)
    (rows : Fin D → List C) (hL : ∀ i, (rows i).length ≤ L) :
    (buildTaylorProgram ops.program θ q rows).callbackCost ≤ D * (4 * L ^ 2 + 1) * B := by
  simp only [buildTaylorProgram, Array.toList_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin D, (4 * L ^ 2 + 1) * B := by
      apply Finset.sum_le_sum
      intro i _
      exact (buildRowProgram_cost ops budget θ q (rows i)).trans (by gcongr; exact hL i)
    _ = _ := by simp; ring

omit budget

theorem buildTaylorProgram_reads {D : ℕ} (θ : C) (q : ℕ) (rows : Fin D → List C) :
    (buildTaylorProgram ops.program θ q rows).listReads ≤ D * (q + 1) ^ 2 := by
  simp only [buildTaylorProgram, Array.toList_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin D, (q + 1) ^ 2 :=
      Finset.sum_le_sum (fun i _ => buildRowProgram_reads ops θ q (rows i))
    _ = _ := by simp

include budget

theorem buildCodeTaylorProgram_compileCost {D : ℕ} (θ : C) (q W : ℕ)
    (rows : Fin D → PolynomialCode C) (hW : ∀ i, SubexpTaylorCode.codeWeight (rows i) ≤ W) :
    (buildCodeTaylorProgram ops.program θ q rows).compileCost ≤ 4 * D * W ^ 2 * B := by
  simp only [buildCodeTaylorProgram, Array.toList_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin D, 4 * W ^ 2 * B := by
      apply Finset.sum_le_sum
      intro i _
      exact (compileCodeProgram_cost ops budget (rows i)).trans (by gcongr; exact hW i)
    _ = _ := by simp; ring

theorem buildCodeTaylorProgram_shiftCost {D : ℕ} (θ : C) (q L : ℕ)
    (rows : Fin D → PolynomialCode C)
    (hL : ∀ i, SubexpTaylorCode.codeLengthBound (rows i) ≤ L) :
    (buildCodeTaylorProgram ops.program θ q rows).taylor.callbackCost ≤ D * (4 * L ^ 2 + 1) * B := by
  rw [buildCodeTaylorProgram_taylor]
  exact buildTaylorProgram_cost ops budget θ q L _
    (fun i => (compileCodeProgram_length ops (rows i)).trans (hL i))

omit budget

theorem buildCodeTaylorProgram_reads {D : ℕ} (θ : C) (q : ℕ)
    (rows : Fin D → PolynomialCode C) :
    (buildCodeTaylorProgram ops.program θ q rows).taylor.listReads ≤ D * (q + 1) ^ 2 := by
  rw [buildCodeTaylorProgram_taylor]
  exact buildTaylorProgram_reads ops θ q _

include budget

theorem buildFactorProgram_compileCost {D p r : ℕ} {K : Type*} (θ : C) (q W : ℕ)
    (source : SubexpFactorCode.FactorSource D p r K C)
    (hW : ∀ i w, SubexpTaylorCode.codeWeight (source.rows i w) ≤ W) :
    (buildFactorProgram ops.program θ q source).compileCost ≤ 4 * source.arity * D * W ^ 2 * B := by
  simp only [buildFactorProgram, Array.toList_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin source.arity, 4 * D * W ^ 2 * B :=
      Finset.sum_le_sum (fun i _ => buildCodeTaylorProgram_compileCost ops budget θ q W _ (hW i))
    _ = _ := by simp; ring

theorem buildFactorProgram_shiftCost {D p r : ℕ} {K : Type*} (θ : C) (q L : ℕ)
    (source : SubexpFactorCode.FactorSource D p r K C)
    (hL : ∀ i w, SubexpTaylorCode.codeLengthBound (source.rows i w) ≤ L) :
    (buildFactorProgram ops.program θ q source).shiftCost ≤ source.arity * D * (4 * L ^ 2 + 1) * B := by
  simp only [buildFactorProgram, Array.toList_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin source.arity, D * (4 * L ^ 2 + 1) * B :=
      Finset.sum_le_sum (fun i _ => buildCodeTaylorProgram_shiftCost ops budget θ q L _ (hL i))
    _ = _ := by simp; ring

omit budget

theorem buildFactorProgram_reads {D p r : ℕ} {K : Type*} (θ : C) (q : ℕ)
    (source : SubexpFactorCode.FactorSource D p r K C) :
    (buildFactorProgram ops.program θ q source).listReads ≤ source.arity * D * (q + 1) ^ 2 := by
  simp only [buildFactorProgram, Array.toList_ofFn, List.map_ofFn, Function.comp_def, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin source.arity, D * (q + 1) ^ 2 :=
      Finset.sum_le_sum (fun i _ => buildCodeTaylorProgram_reads ops θ q _)
    _ = _ := by simp; ring

include budget

theorem buildFactorsProgram_compileCost {D p r : ℕ} {K : Type*} (θ : C) (q W : ℕ)
    (sources : List (SubexpFactorCode.FactorSource D p r K C))
    (hW : ∀ source ∈ sources, ∀ i w, SubexpTaylorCode.codeWeight (source.rows i w) ≤ W) :
    (buildFactorsProgram ops.program θ q sources).compileCost ≤
      4 * SubexpFactorCode.incidenceCount sources * D * W ^ 2 * B := by
  induction sources with
  | nil => simp [buildFactorsProgram]
  | cons source sources ih =>
      have hf := buildFactorProgram_compileCost ops budget θ q W source (hW source (by simp))
      have ht := ih (fun s hs => hW s (by simp [hs]))
      change _ + _ ≤ _
      rw [SubexpFactorCode.incidenceCount_cons]
      calc
        _ ≤ 4 * source.arity * D * W ^ 2 * B +
            4 * SubexpFactorCode.incidenceCount sources * D * W ^ 2 * B := Nat.add_le_add hf ht
        _ = _ := by ring

theorem buildFactorsProgram_shiftCost {D p r : ℕ} {K : Type*} (θ : C) (q L : ℕ)
    (sources : List (SubexpFactorCode.FactorSource D p r K C))
    (hL : ∀ source ∈ sources, ∀ i w, SubexpTaylorCode.codeLengthBound (source.rows i w) ≤ L) :
    (buildFactorsProgram ops.program θ q sources).shiftCost ≤
      SubexpFactorCode.incidenceCount sources * D * (4 * L ^ 2 + 1) * B := by
  induction sources with
  | nil => simp [buildFactorsProgram]
  | cons source sources ih =>
      have hf := buildFactorProgram_shiftCost ops budget θ q L source (hL source (by simp))
      have ht := ih (fun s hs => hL s (by simp [hs]))
      change _ + _ ≤ _
      rw [SubexpFactorCode.incidenceCount_cons]
      calc
        _ ≤ source.arity * D * (4 * L ^ 2 + 1) * B +
            SubexpFactorCode.incidenceCount sources * D * (4 * L ^ 2 + 1) * B := Nat.add_le_add hf ht
        _ = _ := by ring

omit budget

theorem buildFactorsProgram_reads {D p r : ℕ} {K : Type*} (θ : C) (q : ℕ)
    (sources : List (SubexpFactorCode.FactorSource D p r K C)) :
    (buildFactorsProgram ops.program θ q sources).listReads ≤
      SubexpFactorCode.incidenceCount sources * D * (q + 1) ^ 2 := by
  induction sources with
  | nil => simp [buildFactorsProgram]
  | cons source sources ih =>
      have hf := buildFactorProgram_reads ops θ q source
      change _ + _ ≤ _
      rw [SubexpFactorCode.incidenceCount_cons]
      calc
        _ ≤ source.arity * D * (q + 1) ^ 2 +
            SubexpFactorCode.incidenceCount sources * D * (q + 1) ^ 2 := Nat.add_le_add hf ih
        _ = _ := by ring

end Correctness

/-- Actual prepared binary callbacks instantiate the complete frontend; the
runtime arguments contain no semantic ring decoder or cost-bound certificate. -/
def preparedFactors {K : Type*} (p D r : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t z o θ : SubexpSymbolicCost.QuarticCode p D) (q : ℕ)
    (sources : List (SubexpFactorCode.FactorSource D p r K (SubexpSymbolicCost.QuarticCode p D))) :=
  buildFactorsProgram (SubexpSymbolicCost.preparedProgram p D M t z o) θ q sources

theorem preparedFactors_bounds {K : Type*} (p D r : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1)) (c : Fin 4 → ZMod (p ^ (D + 1)))
    (t z o θ : SubexpSymbolicCost.QuarticCode p D)
    (ht : t.map (SubexpQuarticRing.wordValue p (D + 1)) = SubexpQuarticRing.reductionData c)
    (hz : SubexpQuarticRing.quotientDenote c (z.map (SubexpQuarticRing.wordValue p (D + 1))) = 0)
    (ho : SubexpQuarticRing.quotientDenote c (o.map (SubexpQuarticRing.wordValue p (D + 1))) = 1)
    (q W L : ℕ)
    (sources : List (SubexpFactorCode.FactorSource D p r K (SubexpSymbolicCost.QuarticCode p D)))
    (hW : ∀ source ∈ sources, ∀ i w, SubexpTaylorCode.codeWeight (source.rows i w) ≤ W)
    (hL : ∀ source ∈ sources, ∀ i w, SubexpTaylorCode.codeLengthBound (source.rows i w) ≤ L) :
    (preparedFactors p D r M t z o θ q sources).compileCost ≤
        4 * SubexpFactorCode.incidenceCount sources * D * W ^ 2 *
          SubexpSymbolicCost.quarticEventBudget D (Nat.log 2 p + 1) ∧
      (preparedFactors p D r M t z o θ q sources).shiftCost ≤
        SubexpFactorCode.incidenceCount sources * D * (4 * L ^ 2 + 1) *
          SubexpSymbolicCost.quarticEventBudget D (Nat.log 2 p + 1) ∧
      (preparedFactors p D r M t z o θ q sources).listReads ≤
        SubexpFactorCode.incidenceCount sources * D * (q + 1) ^ 2 := by
  let ops := SubexpSymbolicCost.preparedRing p D M c t z o ht hz ho
  have hb := SubexpSymbolicCost.preparedRing_budget p D M c t z o ht hz ho
  simpa only [ops, SubexpSymbolicCost.preparedRing_program, preparedFactors] using
    And.intro (buildFactorsProgram_compileCost ops hb θ q W sources hW)
      (And.intro (buildFactorsProgram_shiftCost ops hb θ q L sources hL)
        (buildFactorsProgram_reads ops θ q sources))

end SubexponentialSAT.SubexpTaylorExecution

end OAI.Algorithms
