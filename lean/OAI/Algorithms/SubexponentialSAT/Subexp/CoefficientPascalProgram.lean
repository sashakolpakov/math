import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientDynamics
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScalarProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding

namespace OAI.Algorithms

/-! # The actual modular Pascal update used by coefficient search -/

namespace SubexponentialSAT.Subexp.CoefficientPascalProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram MatrixWordEncoding

variable (p : ℕ) [Fact p.Prime]

theorem add_field_eval (x y : ZMod p) (regs : Fin 8 → Bool)
    (acc left right saved output zero input : List Bool) :
    ∃ n ≤ 6000 * (width p + 1) ^ 2, ∃ regs',
      Eval add n
        (state regs (word p x) (word p y) (modulus p) acc left right saved output zero input)
        (state regs' (word p (x + y)) [] (modulus p) acc left right saved output zero input) := by
  obtain ⟨n,hn,r,result,he,hl,hv⟩ := add_eval regs (word p x) (word p y) (modulus p)
    acc left right saved output zero input (width p) (word_length p x) (word_length p y)
    (by simp) (modulus_positive p) (by simpa only [modulus_value] using modulus_capacity p)
  have hc : BinaryArithmetic.toNat result < p := by
    rw [hv,modulus_value]
    exact Nat.mod_lt _ (Fact.out : p.Prime).pos
  have hf : (BinaryArithmetic.toNat result : ZMod p) = x + y := by
    rw [hv,modulus_value,ZMod.natCast_mod,Nat.cast_add,word_field_value,word_field_value]
  have hr := word_unique p (x + y) result hl hc hf
  subst result
  exact ⟨n,hn,r,he⟩

abbrev doubleCell : Cmd 8 16 :=
  .seq (MatrixProgramSupport.copy 1 8 9)
    (.seq add (.seq (move 8 1 9) add))

def cellBudget (B : ℕ) : ℕ := 12000 * (B + 1) ^ 2 + 13 * B + 11

theorem doubleCell_eval (x y : ZMod p) (regs : Fin 8 → Bool)
    (left right saved output zero input : List Bool) :
    ∃ n ≤ cellBudget (width p), ∃ regs',
      Eval doubleCell n
        (state regs (word p x) (word p y) (modulus p) [] left right saved output zero input)
        (state regs' (word p (x + 2 * y)) [] (modulus p) [] left right saved output zero input) := by
  obtain ⟨a,ha,hsa⟩ := MatrixProgramSupport.copy_eval (1 : Fin 16) 8 9
    (by decide) (by decide) (by decide)
    (state regs (word p x) (word p y) (modulus p) [] left right saved output zero input) rfl
  have hstateA : a = state a.regs (word p x) (word p y) (modulus p)
      (word p y) left right saved output zero input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext j
    fin_cases j <;> simp [scalarStacks,StackRoutines.copyStacks]
  rw [hstateA] at ha
  obtain ⟨n₁,hn₁,r₁,h₁⟩ := add_field_eval p x y a.regs
    (word p y) left right saved output zero input
  obtain ⟨b,hb,hsb⟩ := move_eval (8 : Fin 16) 1 9
    (by decide) (by decide) (by decide)
    (state r₁ (word p (x + y)) [] (modulus p) (word p y) left right saved output zero input)
    rfl rfl
  have hstateB : b = state b.regs (word p (x + y)) (word p y) (modulus p)
      [] left right saved output zero input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsb]
    funext j
    fin_cases j <;> simp [scalarStacks]
  rw [hstateB] at hb
  obtain ⟨n₂,hn₂,r₂,h₂⟩ := add_field_eval p (x + y) y b.regs
    [] left right saved output zero input
  have hvalue : x + y + y = x + 2 * y := by ring
  rw [hvalue] at h₂
  have he := ha.seq (h₁.seq (hb.seq h₂))
  refine ⟨7 * width p + 5 + (n₁ + (6 * width p + 6 + n₂)),?_,r₂,?_⟩
  · dsimp [cellBudget]
    omega
  · simpa [doubleCell,state,scalarStacks,word_length] using he

def combine (double : Bool) (x y : ZMod p) : ZMod p :=
  if double then x + 2 * y else x + y

abbrev cell (double : Bool) : Cmd 8 16 := if double then doubleCell else add

theorem cell_eval (double : Bool) (x y : ZMod p) (regs : Fin 8 → Bool)
    (left right saved output zero input : List Bool) :
    ∃ n ≤ cellBudget (width p), ∃ regs',
      Eval (cell double) n
        (state regs (word p x) (word p y) (modulus p) [] left right saved output zero input)
        (state regs' (word p (combine p double x y)) [] (modulus p) []
          left right saved output zero input) := by
  cases double with
  | false =>
      obtain ⟨n,hn,r,he⟩ := add_field_eval p x y regs [] left right saved output zero input
      exact ⟨n,by dsimp [cellBudget]; omega,r,by simpa [cell,combine] using he⟩
  | true => simpa [cell,combine] using doubleCell_eval p x y regs left right saved output zero input

abbrev row (double : Bool) : Cmd 8 16 :=
  .seq (readWord 10 0 9 (by decide))
    (.seq (readWord 11 1 9 (by decide))
      (.seq (cell double) (.seq (emitFrame 0 8 9 (by decide)) (transfer 8 13))))

def rowBudget (B : ℕ) : ℕ := 12000 * (B + 1) ^ 2 + 45 * B + 39

theorem row_eval (double : Bool) (x y : ZMod p) (regs : Fin 8 → Bool)
    (left right saved output zero input : List Bool) :
    ∃ n ≤ rowBudget (width p), ∃ regs',
      Eval (row double) n
        (state regs [] [] (modulus p) []
          (Encoding.frame (word p x) ++ left) (Encoding.frame (word p y) ++ right)
          saved output zero input)
        (state regs' [] [] (modulus p) [] left right saved
          ((Encoding.frame (word p (combine p double x y))).reverse ++ output) zero input) := by
  obtain ⟨a,ha,hsa⟩ := readWord_eval (10 : Fin 16) 0 9
    (by decide) (by decide) (by decide)
    (state regs [] [] (modulus p) []
      (Encoding.frame (word p x) ++ left) (Encoding.frame (word p y) ++ right)
      saved output zero input)
    (word p x) left rfl rfl rfl
  have hstateA : a = state a.regs (word p x) [] (modulus p) [] left
      (Encoding.frame (word p y) ++ right) saved output zero input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext j
    fin_cases j <;> simp [scalarStacks]
  rw [hstateA] at ha
  obtain ⟨b,hb,hsb⟩ := readWord_eval (11 : Fin 16) 1 9
    (by decide) (by decide) (by decide)
    (state a.regs (word p x) [] (modulus p) [] left
      (Encoding.frame (word p y) ++ right) saved output zero input)
    (word p y) right rfl rfl rfl
  have hstateB : b = state b.regs (word p x) (word p y) (modulus p) []
      left right saved output zero input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsb]
    funext j
    fin_cases j <;> simp [scalarStacks]
  rw [hstateB] at hb
  obtain ⟨n,hn,r,hr⟩ := cell_eval p double x y b.regs left right saved output zero input
  obtain ⟨c,hc,hsc⟩ := emitFrame_eval (0 : Fin 16) 8 9
    (by decide) (by decide) (by decide)
    (state r (word p (combine p double x y)) [] (modulus p) [] left right saved output zero input) rfl
  have hstateC : c = state c.regs [] [] (modulus p)
      (Encoding.frame (word p (combine p double x y))) left right saved output zero input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsc]
    funext j
    fin_cases j <;> simp [scalarStacks]
  rw [hstateC] at hc
  obtain ⟨d,hd,hsd⟩ := transfer_eval (8 : Fin 16) 13 (by decide)
    (state c.regs [] [] (modulus p)
      (Encoding.frame (word p (combine p double x y))) left right saved output zero input)
  have hstateD : d = state d.regs [] [] (modulus p) [] left right saved
      ((Encoding.frame (word p (combine p double x y))).reverse ++ output) zero input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsd]
    funext j
    fin_cases j <;> simp [scalarStacks,StackRoutines.transferStacks]
  rw [hstateD] at hd
  have he := ha.seq (hb.seq (hr.seq (hc.seq hd)))
  refine ⟨(9 * width p + 7) + ((9 * width p + 7) +
    (n + ((8 * width p + 8) + (3 * (2 * width p + 1) + 3)))),?_,d.regs,?_⟩
  · dsimp [rowBudget,cellBudget] at *
    omega
  · simpa [row,state,scalarStacks,word_length,Encoding.length_frame] using he

def valueWords (xs : List (ZMod p)) : List Bool := words (xs.map (word p))

omit [Fact (Nat.Prime p)] in
@[simp] theorem valueWords_nil : valueWords p [] = [] := rfl

omit [Fact (Nat.Prime p)] in
@[simp] theorem valueWords_cons (x : ZMod p) (xs : List (ZMod p)) :
    valueWords p (x :: xs) = Encoding.frame (word p x) ++ valueWords p xs := rfl

omit [Fact (Nat.Prime p)] in
theorem valueWords_length (xs : List (ZMod p)) :
    (valueWords p xs).length = xs.length * (2 * width p + 1) := by
  unfold valueWords
  rw [words_length (xs.map (word p)) (width p)]
  · simp
  · intro w hw
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hw
    exact word_length p x

def pairValues (double : Bool) (xs ys : List (ZMod p)) : List (ZMod p) :=
  List.zipWith (combine p double) xs ys

abbrev popCount : Cmd 8 16 := .base (.atom (.pop 15 0 1))
abbrev loopBody (double : Bool) : Cmd 8 16 := .seq (row double) popCount
abbrev pairLoop (double : Bool) : Cmd 8 16 := .while 1 (loopBody double)

def ready (regs : Fin 8 → Bool) (left right saved output zero : List Bool) (n : ℕ) :
    MatrixScalarProgram.Data :=
  state (readRegs regs 0 1 (List.replicate n true).head?) [] [] (modulus p) []
    left right saved output zero (List.replicate n true).tail

omit [Fact (Nat.Prime p)] in
theorem popCount_eval (regs : Fin 8 → Bool) (left right saved output zero : List Bool) (n : ℕ) :
    Eval popCount 1
      (state regs [] [] (modulus p) [] left right saved output zero (List.replicate n true))
      (ready p regs left right saved output zero n) := by
  let a := state regs [] [] (modulus p) [] left right saved output zero (List.replicate n true)
  have h := Eval.base (StructuredProgram.Eval.atom (.pop 15 0 1) a)
  have he : (StructuredProgram.Atom.pop 15 0 1).eval a =
      ready p regs left right saved output zero n := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    funext j
    fin_cases j <;> simp [a,ready,state,scalarStacks,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
  rw [he] at h
  exact h

omit [Fact (Nat.Prime p)] in
theorem ready_zero (regs : Fin 8 → Bool) (left right saved output zero : List Bool) :
    (ready p regs left right saved output zero 0).regs 1 = false := by
  simp [ready,state,readRegs]

omit [Fact (Nat.Prime p)] in
theorem ready_succ (regs : Fin 8 → Bool) (left right saved output zero : List Bool) (n : ℕ) :
    (ready p regs left right saved output zero (n + 1)).regs 1 = true := by
  simp [ready,state,readRegs,List.replicate_succ]

theorem pairLoop_eval (double : Bool) (xs ys : List (ZMod p)) (hlen : xs.length = ys.length)
    (regs : Fin 8 → Bool) (left right saved output zero : List Bool) :
    ∃ n ≤ xs.length * (rowBudget (width p) + 2) + 1, ∃ regs',
      Eval (pairLoop double) n
        (ready p regs (valueWords p xs ++ left) (valueWords p ys ++ right)
          saved output zero xs.length)
        (state regs' [] [] (modulus p) [] left right saved
          ((valueWords p (pairValues p double xs ys)).reverse ++ output) zero []) := by
  induction xs generalizing ys regs output with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      refine ⟨1,by simp,(ready p regs left right saved output zero 0).regs,?_⟩
      simpa [pairLoop,ready,pairValues,state] using
        (Eval.while_false (test := (1 : Fin 8)) (body := loopBody double)
          (ready_zero p regs left right saved output zero))
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length = ys.length := Nat.succ.inj hlen
          let r := (ready p regs (valueWords p (x :: xs) ++ left)
            (valueWords p (y :: ys) ++ right) saved output zero (x :: xs).length).regs
          obtain ⟨nr,hnr,rr,hr⟩ := row_eval p double x y r
            (valueWords p xs ++ left) (valueWords p ys ++ right) saved output zero
            (List.replicate xs.length true)
          have hrow : Eval (row double) nr
              (ready p regs (valueWords p (x :: xs) ++ left)
                (valueWords p (y :: ys) ++ right) saved output zero (x :: xs).length)
              (state rr [] [] (modulus p) [] (valueWords p xs ++ left)
                (valueWords p ys ++ right) saved
                ((Encoding.frame (word p (combine p double x y))).reverse ++ output) zero
                (List.replicate xs.length true)) := by
            simpa only [r,ready,valueWords_cons,List.length_cons,List.replicate_succ,
              List.tail_cons,List.append_assoc] using hr
          have hp := popCount_eval p rr (valueWords p xs ++ left) (valueWords p ys ++ right)
            saved ((Encoding.frame (word p (combine p double x y))).reverse ++ output) zero xs.length
          obtain ⟨nt,hnt,rf,ht⟩ := ih ys htail rr
            ((Encoding.frame (word p (combine p double x y))).reverse ++ output)
          have hrun := Eval.while_true
            (ready_succ p regs (valueWords p (x :: xs) ++ left)
              (valueWords p (y :: ys) ++ right) saved output zero xs.length)
            (hrow.seq hp) ht
          refine ⟨(nr + 1) + nt + 1,?_,rf,?_⟩
          · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
            omega
          · simpa only [pairLoop,loopBody,pairValues,List.zipWith_cons_cons,valueWords_cons,
              List.reverse_append,List.append_assoc, List.length_cons] using hrun

def successors (xs : List (ZMod p)) : List (ZMod p) := (xs ++ [0]).tail

@[simp] theorem successors_length (xs : List (ZMod p)) :
    (successors p xs).length = xs.length := by
  simp [successors]

omit [Fact (Nat.Prime p)] in
theorem valueWords_append (xs ys : List (ZMod p)) :
    valueWords p (xs ++ ys) = valueWords p xs ++ valueWords p ys := by
  simp only [valueWords,List.map_append,words_append]

theorem words_first_successors (xs : List (ZMod p)) :
    valueWords p xs ++ Encoding.frame (word p 0) =
      Encoding.frame (word p (xs.getD 0 0)) ++ valueWords p (successors p xs) := by
  cases xs <;> simp [successors,valueWords_append,List.append_assoc]

def shiftBy (double : Bool) : List (ZMod p) → List (ZMod p)
  | [] => []
  | x :: xs => combine p double x (xs.getD 0 0) :: shiftBy double xs

@[simp] theorem shiftBy_length (double : Bool) (xs : List (ZMod p)) :
    (shiftBy p double xs).length = xs.length := by
  induction xs <;> simp [shiftBy, *]

theorem shiftBy_true (xs : List (ZMod p)) :
    shiftBy p true xs = CoefficientDynamics.shift xs := by
  induction xs <;> simp [shiftBy,combine,CoefficientDynamics.shift, *]

theorem shiftBy_false (xs : List (ZMod p)) :
    shiftBy p false xs =
      List.zipWith (· + ·) xs (successors p xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp [shiftBy,combine,successors]
      | cons y ys =>
          simpa [shiftBy,combine,successors] using congrArg (List.cons (x + y)) ih

theorem pairValues_successors (double : Bool) (xs : List (ZMod p)) :
    pairValues p double xs (successors p xs) = shiftBy p double xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases xs with
      | nil => simp [pairValues,successors,shiftBy]
      | cons y ys =>
          simpa [pairValues,successors,shiftBy] using
            congrArg (List.cons (combine p double x y)) ih

abbrev setup : Cmd 8 16 :=
  .seq (MatrixProgramSupport.copy 14 0 9)
    (.seq (emitFrame 0 11 9 (by decide))
      (.seq (MatrixProgramSupport.copy 12 11 9)
        (.seq (MatrixProgramSupport.copy 12 10 9)
          (.seq (readWord 11 0 9 (by decide))
            (.call (StackRoutines.clearProgram 0 0 1))))))

def setupBudget (R B : ℕ) : ℕ := 14 * (R * (2 * B + 1)) + 26 * B + 33

theorem setup_eval (xs : List (ZMod p)) (regs : Fin 8 → Bool)
    (output input : List Bool) :
    ∃ n ≤ setupBudget xs.length (width p), ∃ regs',
      Eval setup n
        (state regs [] [] (modulus p) [] [] [] (valueWords p xs) output (word p 0) input)
        (state regs' [] [] (modulus p) [] (valueWords p xs)
          (valueWords p (successors p xs)) (valueWords p xs) output (word p 0) input) := by
  obtain ⟨a,ha,hsa⟩ := MatrixProgramSupport.copy_eval (14 : Fin 16) 0 9
    (by decide) (by decide) (by decide)
    (state regs [] [] (modulus p) [] [] [] (valueWords p xs) output (word p 0) input) rfl
  have hA : a = state a.regs (word p 0) [] (modulus p) [] [] []
      (valueWords p xs) output (word p 0) input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsa]
    funext j
    fin_cases j <;> simp [scalarStacks,StackRoutines.copyStacks]
  rw [hA] at ha
  obtain ⟨b,hb,hsb⟩ := emitFrame_eval (0 : Fin 16) 11 9
    (by decide) (by decide) (by decide)
    (state a.regs (word p 0) [] (modulus p) [] [] []
      (valueWords p xs) output (word p 0) input) rfl
  have hB : b = state b.regs [] [] (modulus p) [] [] (Encoding.frame (word p 0))
      (valueWords p xs) output (word p 0) input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsb]
    funext j
    fin_cases j <;> simp [scalarStacks]
  rw [hB] at hb
  obtain ⟨c,hc,hsc⟩ := MatrixProgramSupport.copy_eval (12 : Fin 16) 11 9
    (by decide) (by decide) (by decide)
    (state b.regs [] [] (modulus p) [] [] (Encoding.frame (word p 0))
      (valueWords p xs) output (word p 0) input) rfl
  have hC : c = state c.regs [] [] (modulus p) [] []
      (valueWords p xs ++ Encoding.frame (word p 0))
      (valueWords p xs) output (word p 0) input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsc]
    funext j
    fin_cases j <;> simp [scalarStacks,StackRoutines.copyStacks]
  rw [hC] at hc
  obtain ⟨d,hd,hsd⟩ := MatrixProgramSupport.copy_eval (12 : Fin 16) 10 9
    (by decide) (by decide) (by decide)
    (state c.regs [] [] (modulus p) [] []
      (valueWords p xs ++ Encoding.frame (word p 0))
      (valueWords p xs) output (word p 0) input) rfl
  have hD : d = state d.regs [] [] (modulus p) [] (valueWords p xs)
      (valueWords p xs ++ Encoding.frame (word p 0))
      (valueWords p xs) output (word p 0) input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsd]
    funext j
    fin_cases j <;> simp [scalarStacks,StackRoutines.copyStacks]
  rw [hD] at hd
  obtain ⟨e,he,hse⟩ := readWord_eval (11 : Fin 16) 0 9
    (by decide) (by decide) (by decide)
    (state d.regs [] [] (modulus p) [] (valueWords p xs)
      (valueWords p xs ++ Encoding.frame (word p 0))
      (valueWords p xs) output (word p 0) input)
    (word p (xs.getD 0 0)) (valueWords p (successors p xs))
    (words_first_successors p xs) rfl rfl
  have hE : e = state e.regs (word p (xs.getD 0 0)) [] (modulus p) [] (valueWords p xs)
      (valueWords p (successors p xs)) (valueWords p xs) output (word p 0) input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hse]
    funext j
    fin_cases j <;> simp [scalarStacks]
  rw [hE] at he
  have hf := Subexp.TupleProgram.clear_eval (0 : Fin 16) (0 : Fin 8) 1
    (state e.regs (word p (xs.getD 0 0)) [] (modulus p) [] (valueWords p xs)
      (valueWords p (successors p xs)) (valueWords p xs) output (word p 0) input)
  let r := readRegs e.regs 0 1 none
  have hF : (⟨r,StackRoutines.clearStacks 0
      (state e.regs (word p (xs.getD 0 0)) [] (modulus p) [] (valueWords p xs)
        (valueWords p (successors p xs)) (valueWords p xs) output (word p 0) input).stacks⟩ :
        MatrixScalarProgram.Data) =
      state r [] [] (modulus p) [] (valueWords p xs)
        (valueWords p (successors p xs)) (valueWords p xs) output (word p 0) input := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    funext j
    fin_cases j <;> simp [scalarStacks,StackRoutines.clearStacks]
  change Eval _ _ _ (⟨r,_⟩ : MatrixScalarProgram.Data) at hf
  rw [hF] at hf
  have ht := ha.seq (hb.seq (hc.seq (hd.seq (he.seq hf))))
  refine ⟨setupBudget xs.length (width p),le_rfl,r,?_⟩
  convert ht using 1 ;
    simp [setupBudget,scalarStacks,word_length,valueWords_length] ; ring

abbrev command (double : Bool) : Cmd 8 16 :=
  .seq setup (.seq popCount (.seq (pairLoop double) (transfer 13 8)))

def program (double : Bool) := compiled (command double) 12 8

def budget (R B : ℕ) : ℕ :=
  setupBudget R B + R * (rowBudget B + 2) + 3 * (R * (2 * B + 1)) + 6

theorem program_run (double : Bool) (xs : List (ZMod p)) (regs : Fin 8 → Bool) :
    ∃ regs', RunsIn (program double) (budget xs.length (width p))
      ((state regs [] [] (modulus p) [] [] [] (valueWords p xs) [] (word p 0)
        (List.replicate xs.length true)).withPC (some (program double).entry))
      ((state regs' [] [] (modulus p) (valueWords p (shiftBy p double xs)) [] []
        (valueWords p xs) [] (word p 0) []).withPC none) := by
  obtain ⟨ns,hns,rs,hs⟩ := setup_eval p xs regs [] (List.replicate xs.length true)
  have hp := popCount_eval p rs (valueWords p xs) (valueWords p (successors p xs))
    (valueWords p xs) [] (word p 0) xs.length
  obtain ⟨nl,hnl,rl,hl⟩ := pairLoop_eval p double xs (successors p xs) (successors_length p xs).symm
    rs [] [] (valueWords p xs) [] (word p 0)
  simp only [List.append_nil,pairValues_successors] at hl
  obtain ⟨d,hd,hsd⟩ := transfer_eval (13 : Fin 16) 8 (by decide)
    (state rl [] [] (modulus p) [] [] [] (valueWords p xs)
      (valueWords p (shiftBy p double xs)).reverse (word p 0) [])
  have hD : d = state d.regs [] [] (modulus p) (valueWords p (shiftBy p double xs))
      [] [] (valueWords p xs) [] (word p 0) [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hsd]
    funext j
    fin_cases j <;> simp [scalarStacks,StackRoutines.transferStacks]
  rw [hD] at hd
  have ht := hs.seq (hp.seq (hl.seq hd))
  refine ⟨d.regs,_,?_,compiled_halt_trace ht 12 8⟩
  have hlen : (valueWords p (shiftBy p double xs)).length =
      xs.length * (2 * width p + 1) := by
    rw [valueWords_length,shiftBy_length]
  change ns + (1 + (nl + (3 * (valueWords p (shiftBy p double xs)).reverse.length + 3))) + 1 ≤ _
  rw [List.length_reverse,hlen]
  dsimp [budget]
  omega

end SubexponentialSAT.Subexp.CoefficientPascalProgram

end OAI.Algorithms
