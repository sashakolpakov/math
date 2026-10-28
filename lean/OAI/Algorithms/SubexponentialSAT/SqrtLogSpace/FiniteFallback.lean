import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.EncodingBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
import Mathlib.Data.Fintype.EquivFin
import OAI.Algorithms.SubexponentialSAT.BitProgram
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Sigma
import Lean.Elab.Tactic.Omega

/-! Generic finite scanner selectively adapted from the reviewed canceled source
`CountingDraft/FiniteWordScanner.lean`; no obsolete endpoint or rate is imported.

Fixed finite control for bounded input prefixes and complete binary output words.
The transition table is chosen before any runtime input. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner


def BoundedWord (M : ℕ) := {word : List Bool // word.length ≤ M}

noncomputable instance boundedWordFintype (M : ℕ) : Fintype (BoundedWord M) :=
  Fintype.ofInjective
    (fun w => (⟨⟨w.val.length, by have := w.property; omega⟩, ⟨w.val, rfl⟩⟩ :
      (i : Fin (M + 1)) × List.Vector Bool i.val))
    (by
      intro a b h
      exact Subtype.ext (congrArg (fun v : (i : Fin (M + 1)) × List.Vector Bool i.val => v.2.val) h))

/-- `none` is a single overflow state. Bounded prefes occupy fixed finite control. -/
def boundedNext (M : ℕ) : Option (BoundedWord M) → Bool → Option (BoundedWord M)
  | none, _ => none
  | some pref, bit =>
      if h : pref.val.length < M then
        some ⟨pref.val ++ [bit], by simp; omega⟩
      else none

theorem bounded_fold (M : ℕ) (pref word : List Bool)
    (h : pref.length + word.length ≤ M) :
    word.foldl (boundedNext M)
      (some ⟨pref, by omega⟩) =
        some ⟨pref ++ word, by simpa using h⟩ := by
  induction word generalizing pref with
  | nil => simp
  | cons bit word ih =>
      have hp : pref.length < M := by
        simp only [List.length_cons] at h
        omega
      have ht : (pref ++ [bit]).length + word.length ≤ M := by
        simp only [List.length_append, List.length_singleton] at *
        simp only [List.length_cons] at h
        omega
      simpa [boundedNext, hp, List.append_assoc] using ih (pref ++ [bit]) ht

theorem bounded_fold_empty (M : ℕ) (word : List Bool) (h : word.length ≤ M) :
    word.foldl (boundedNext M) (some ⟨[], Nat.zero_le M⟩) = some ⟨word, h⟩ := by
  simpa using bounded_fold M [] word (by simpa using h)

noncomputable def finiteOutputBound {Q : Type*} [Fintype Q] (out : Q → List Bool) : ℕ :=
  Finset.univ.sup fun q => (out q).length

theorem length_le_finiteOutputBound {Q : Type*} [Fintype Q]
    (out : Q → List Bool) (q : Q) :
    (out q).length ≤ finiteOutputBound out :=
  Finset.le_sup (f := fun q => (out q).length) (Finset.mem_univ q)



open BitProgram

variable {qCount : ℕ}

/-- One fixed table contains the complete output word for each finite scanner state. -/
def labelCount (L : ℕ) : ℕ := qCount * (2 * L + 5)

def addr (L : ℕ) (q : Fin qCount) (i : ℕ) (hi : i < 2 * L + 5) :
    Fin (labelCount (qCount := qCount) L) := finProdFinEquiv (q, ⟨i, hi⟩)

def decode (L : ℕ) (label : Fin (labelCount (qCount := qCount) L)) :
    Fin qCount × Fin (2 * L + 5) := finProdFinEquiv.symm label

@[simp] theorem decode_addr (L : ℕ) (q : Fin qCount) (i : ℕ)
    (hi : i < 2 * L + 5) : decode L (addr L q i hi) = (q, ⟨i, hi⟩) :=
  Equiv.symm_apply_apply finProdFinEquiv _

def regs (value present : Bool) : Fin 2 → Bool :=
  fun i => if i = 0 then value else present

@[simp]theorem update_value (value present next : Bool) :
    Function.update (regs value present) 0 next = regs next present := by
  funext i
  fin_cases i <;> simp [regs]

@[simp]theorem update_present (value present next : Bool) :
    Function.update (regs value present) 1 next = regs value next := by
  funext i
  fin_cases i <;> simp [regs]

@[simp]theorem regs_false : regs false false = fun _ => false := by
  funext i
  simp [regs]

@[simp]theorem update_stack (before after : List Bool) :
    Function.update (fun _ : Fin 1 => before) 0 after = fun _ => after := by
  funext i
  fin_cases i
  simp

@[simp] theorem only_stack (word : List Bool) (i : Fin 1) :
    (if i = 0 then word else []) = word := by
  fin_cases i
  simp

def program (L : ℕ) (start : Fin qCount) (next : Fin qCount → Bool → Fin qCount)
    (out : Fin qCount → List Bool) (hout : ∀ q, (out q).length ≤ L) :
    Program 2 1 (labelCount (qCount := qCount) L) where
  inputStack := 0
  outputStack := 0
  entry := addr L start 0 (by omega)
  code label :=
    let q := (decode L label).1
    let i := (decode L label).2.val
    if i = 0 then .pop 0 0 1 (addr L q 1 (by omega))
    else if i = 1 then .branch 1 (addr L q 2 (by omega)) (addr L q 3 (by omega))
    else if i = 2 then .branch 0
      (addr L (next q true) 0 (by omega)) (addr L (next q false) 0 (by omega))
    else if h : i < 2 * (out q).length + 3 then
      if (i - 3) % 2 = 0 then
        .set 0 ((out q).reverse[(i - 3) / 2]?.getD false)
          (addr L q (i + 1) (by have := hout q; omega))
      else .push 0 0 (addr L q (i + 1) (by have := hout q; omega))
    else if hdone : i = 2 * (out q).length + 3 then
      .set 0 false (addr L q (i + 1) (by have := hout q; omega))
    else .halt

def cfg (L : ℕ) (q : Fin qCount) (i : ℕ) (hi : i < 2 * L + 5)
    (value present : Bool) (word : List Bool) : Cfg 2 1 (labelCount (qCount := qCount) L) :=
  ⟨some (addr L q i hi), regs value present, fun _ => word⟩

variable (L : ℕ) (start : Fin qCount) (next : Fin qCount → Bool → Fin qCount)
  (out : Fin qCount → List Bool) (hout : ∀ q, (out q).length ≤ L)

theorem consume (q : Fin qCount) (value present bit : Bool) (word : List Bool) :
    Trace (program L start next out hout) 3
      (cfg L q 0 (by omega) value present (bit :: word))
      (cfg L (next q bit) 0 (by omega) bit true word) := by
  refine .cons (b := cfg L q 1 (by omega) bit true word) ?_
    (.cons (b := cfg L q 2 (by omega) bit true word) ?_ (.cons ?_ (.refl _)))
  · simp [step, program, cfg, execInstr, readRegs]
  · simp [step, program, cfg, execInstr, regs]
  · cases bit <;> simp [step, program, cfg, execInstr, regs]

theorem begin_output (q : Fin qCount) (value present : Bool) :
    Trace (program L start next out hout) 2
      (cfg L q 0 (by omega) value present [])
      (cfg L q 3 (by omega) false false []) := by
  refine .cons (b := cfg L q 1 (by omega) false false []) ?_ (.cons ?_ (.refl _))
  · simp [step, program, cfg, execInstr, readRegs]
  · simp [step, program, cfg, execInstr]

theorem finish_output (q : Fin qCount) (value : Bool) :
    Trace (program L start next out hout) 2
      (cfg L q (2 * (out q).length + 3) (by have := hout q; omega)
        value false (out q))
      (terminal (program L start next out hout) (out q)) := by
  refine .cons (b := cfg L q (2 * (out q).length + 4) (by have := hout q; omega)
    false false (out q)) ?_ (.cons ?_ (.refl _))
  · simp [step, program, cfg, execInstr]
  · simp [step, program, cfg, execInstr, terminal]

theorem emit_pair (q : Fin qCount) (value bit : Bool) (rest done : List Bool)
    (h : out q = (bit :: rest).reverse ++ done) :
    Trace (program L start next out hout) 2
      (cfg L q (2 * done.length + 3) (by have := hout q; simp [h] at this ⊢; omega)
        value false done)
      (cfg L q (2 * (bit :: done).length + 3)
        (by have := hout q; simp [h] at this ⊢; omega) bit false (bit :: done)) := by
  have hlen : (out q).length = rest.length + 1 + done.length := by simp [h]; omega
  have hbit : ((out q).reverse[done.length]?).getD false = bit := by
    simp [h, List.reverse_append]
  have hfirst : 2 * done.length + 3 < 2 * (out q).length + 3 := by omega
  have hsecond : 2 * done.length + 4 < 2 * (out q).length + 3 := by omega
  refine .cons (b := cfg L q (2 * done.length + 4)
    (by have := hout q; omega) bit false done) ?_ (.cons ?_ (.refl _))
  · simp [step, program, cfg, execInstr, hfirst, hbit,
      show 2 * done.length + 3 ≠ 1 by omega,
      show 2 * done.length + 3 ≠ 2 by omega]
  · simp [step, program, cfg, execInstr, hsecond, regs, Nat.mul_add,
      show 2 * done.length + 4 ≠ 1 by omega,
      show 2 * done.length + 4 ≠ 2 by omega]

theorem emit (q : Fin qCount) (rest done : List Bool) (value : Bool)
    (h : out q = rest.reverse ++ done) :
    Trace (program L start next out hout) (2 * rest.length + 2)
      (cfg L q (2 * done.length + 3) (by have := hout q; simp [h] at this ⊢; omega)
        value false done)
      (terminal (program L start next out hout) (out q)) := by
  induction rest generalizing done value with
  | nil => simpa [h] using finish_output L start next out hout q value
  | cons bit rest ih =>
      have hnext : out q = rest.reverse ++ (bit :: done) := by
        simpa [List.reverse_cons, List.append_assoc] using h
      have ht := (emit_pair L start next out hout q value bit rest done h).trans
        (ih (bit :: done) bit hnext)
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem trace (q : Fin qCount) (word : List Bool) (value present : Bool) :
    Trace (program L start next out hout)
      (3 * word.length + 2 * (out (word.foldl next q)).length + 4)
      (cfg L q 0 (by omega) value present word)
      (terminal (program L start next out hout) (out (word.foldl next q))) := by
  induction word generalizing q value present with
  | nil =>
      rw [List.foldl_nil]
      have ht := (begin_output L start next out hout q value present).trans
        (emit L start next out hout q (out q).reverse [] false (by simp))
      convert ht using 1
      simp only [List.length_reverse, List.length_nil]
      omega
  | cons bit word ih =>
      have ht := (consume L start next out hout q value present bit word).trans
        (ih (next q bit) bit true)
      simpa [List.foldl_cons, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ht

theorem initial_trace (word : List Bool) :
    Trace (program L start next out hout)
      (3 * word.length + 2 * (out (word.foldl next start)).length + 4)
      (initial (program L start next out hout) word)
      (terminal (program L start next out hout) (out (word.foldl next start))) := by
  simpa [initial, program, cfg, regs] using
    trace L start next out hout start word false false


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.Scanner

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback

open BitProgram Scanner
open scoped BigOperators

private def literalPairEquiv (n : ℕ) : (Fin n × Bool) ≃ SAT.Literal (Fin n) where
  toFun p := ⟨p.1, p.2⟩
  invFun l := (l.variable, l.positive)
  left_inv _ := rfl
  right_inv _ := rfl

private instance literalFintype (n : ℕ) : Fintype (SAT.Literal (Fin n)) :=
  Fintype.ofEquiv (Fin n × Bool) (literalPairEquiv n)

/-- The finite domain is fixed by the cutoff, before the input. Ambient variables
are part of the domain and therefore contribute their full free-variable factor. -/
def SmallFormula (B : ℕ) := (n : Fin (B + 1)) × SAT.CNF (Fin n.val)

instance smallFormulaFintype (B : ℕ) : Fintype (SmallFormula B) := by
  unfold SmallFormula
  infer_instance

def smallEncode {B : ℕ} (F : SmallFormula B) : List Bool := Encoding.encodeCNF F.2

theorem smallEncode_injective (B : ℕ) : Function.Injective (smallEncode (B := B)) := by
  rintro ⟨n, F⟩ ⟨m, G⟩ h
  have hn : n = m := Fin.ext (Encoding.encodeCNF_numVariables F G h)
  subst m
  have hF : F = G := Encoding.encodeCNF_injective h
  subst G
  rfl

noncomputable def inputBound (B : ℕ) : ℕ := finiteOutputBound (smallEncode (B := B))

/-- Finite precomputation forms part of the fixed finite transition table. It is
not an input-dependent runtime loop or a unit-cost semantic query. -/
noncomputable def tableCount (B : ℕ) (word : List Bool) : ℕ :=
  ∑ F : SmallFormula B, if smallEncode F = word then SAT.count F.2 else 0

theorem tableCount_code (B : ℕ) (G : SmallFormula B) :
    tableCount B (smallEncode G) = SAT.count G.2 := by
  classical
  have heq (F : SmallFormula B) : smallEncode F = smallEncode G ↔ F = G :=
    (smallEncode_injective B).eq_iff
  simp [tableCount, heq]

noncomputable def outputTable (B : ℕ) : Option (BoundedWord (inputBound B)) → List Bool
  | none => [false]
  | some word => countWord (tableCount B word.val)

noncomputable def countProgram (B : ℕ) :=
  let e := Fintype.equivFin (Option (BoundedWord (inputBound B)))
  program (finiteOutputBound (outputTable B))
    (e (some ⟨[], Nat.zero_le _⟩))
    (fun q bit => e (boundedNext (inputBound B) (e.symm q) bit))
    (fun q => outputTable B (e.symm q))
    (fun q => length_le_finiteOutputBound (outputTable B) (e.symm q))

/-- The real scanner consumes the canonical input and emits every count bit. -/
theorem countProgram_trace (B : ℕ) (F : SmallFormula B) :
    Trace (countProgram B)
      (3 * (smallEncode F).length + 2 * (countWord (SAT.count F.2)).length + 4)
      (initial (countProgram B) (smallEncode F))
      (terminal (countProgram B) (countWord (SAT.count F.2))) := by
  let e := Fintype.equivFin (Option (BoundedWord (inputBound B)))
  have hlen : (smallEncode F).length ≤ inputBound B :=
    length_le_finiteOutputBound _ F
  have heval : (smallEncode F).foldl
      (fun q bit => e (boundedNext (inputBound B) (e.symm q) bit))
      (e (some ⟨[], Nat.zero_le _⟩)) = e (some ⟨smallEncode F, hlen⟩) := by
    rw [List.foldl_hom e (g₁ := boundedNext (inputBound B)) (by intro q bit; simp)]
    rw [bounded_fold_empty _ _ hlen]
  have ht := initial_trace (finiteOutputBound (outputTable B))
    (e (some ⟨[], Nat.zero_le _⟩))
    (fun q bit => e (boundedNext (inputBound B) (e.symm q) bit))
    (fun q => outputTable B (e.symm q))
    (fun q => length_le_finiteOutputBound (outputTable B) (e.symm q)) (smallEncode F)
  rw [heval] at ht
  simpa [countProgram, outputTable, tableCount_code, e] using ht

theorem canonical_count_trace {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B) :
    Trace (countProgram B)
      (3 * Encoding.formulaBitLength F + 2 * (countWord (SAT.count F)).length + 4)
      (initial (countProgram B) (Encoding.encodeCNF F))
      (terminal (countProgram B) (countWord (SAT.count F))) :=
  countProgram_trace B ⟨⟨n, by omega⟩, F⟩

open StructuredCalls

private theorem lift_io {labels steps : ℕ} (p : Program 2 1 labels)
    (input output : List Bool)
    (h : Trace p steps (initial p input) (terminal p output)) :
    Eval (.call (ProgramLinking.liftProgram p (Fin.castAdd 78)
      (fun _ : Fin 1 => ABI.countStack))) steps
      (StructuredProgram.ioState ABI.countStack input)
      (StructuredProgram.ioState ABI.countStack output) := by
  have hs : Function.Injective (fun _ : Fin 1 => ABI.countStack) :=
    fun _ _ _ => Subsingleton.elim _ _
  have he (word : List Bool) :
      embedState (Fin.castAdd 78) (fun _ : Fin 1 => ABI.countStack)
        (StructuredProgram.ioState ABI.countStack input) (StructuredProgram.ioState 0 word) =
          (StructuredProgram.ioState ABI.countStack word : State 80 1220) := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 2 78) hs
    · intro i
      rfl
    · intro i hi
      rfl
    · intro i
      simp [Fin.eq_zero i]
    · intro i hi
      have hne : i ≠ ABI.countStack := by
        intro h
        exact hi ⟨0, h.symm⟩
      simp [hne]
  have hpinput : p.inputStack = 0 := Fin.eq_zero _
  have hpoutput : p.outputStack = 0 := Fin.eq_zero _
  have ht : Trace p steps
      ((StructuredProgram.ioState 0 input).withPC (some p.entry))
      ((StructuredProgram.ioState 0 output).withPC none) := by
    simpa only [initial, terminal, hpinput, hpoutput, StructuredProgram.ioState,
      StructuredProgram.State.withPC] using h
  have hc := eval_call_lifted p (Fin.castAdd 78) (fun _ : Fin 1 => ABI.countStack)
    (StructuredProgram.ioState ABI.countStack input) (Fin.castAdd_injective 2 78) hs ht
  simpa only [he] using hc

/-- The finite count table is called, then a real scan restores the count word
and writes its positivity to the separate answer stack. -/
noncomputable def jointCommand (B : ℕ) : Cmd 80 1220 :=
  .seq (.call (ProgramLinking.liftProgram (countProgram B) (Fin.castAdd 78)
    (fun _ : Fin 1 => ABI.countStack)))
    (Native.positivity Native.positivityPorts ABI.answerStack)

noncomputable def jointProgram (B : ℕ) :=
  compiled (jointCommand B) ABI.countStack ABI.answerStack

noncomputable def countState (word : List Bool) : State 80 1220 :=
  StructuredProgram.ioState ABI.countStack word

noncomputable def finalState (word : List Bool) : State 80 1220 :=
  Native.positivityResult Native.positivityPorts ABI.answerStack (countState word)

theorem jointCommand_eval {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B) :
    Eval (jointCommand B)
      (3 * Encoding.formulaBitLength F + 10 * (countWord (SAT.count F)).length + 12)
      (countState (Encoding.encodeCNF F)) (finalState (countWord (SAT.count F))) := by
  have hc := lift_io (countProgram B) _ _ (canonical_count_trace F hn)
  have hp := Native.positivity_eval Native.positivityPorts ABI.answerStack
    (countState (countWord (SAT.count F)))
    (by simp [countState, StructuredProgram.ioState, Native.positivityPorts,
      ABI.positivityScratch, ABI.countStack])
  have hcounter :
      (countState (countWord (SAT.count F))).stacks Native.positivityPorts.counter =
        countWord (SAT.count F) := by
    change (if ABI.countStack = ABI.countStack then countWord (SAT.count F) else []) = _
    simp
  rw [hcounter] at hp
  have ht := hc.seq hp
  convert ht using 1
  all_goals try rfl
  all_goals omega

theorem jointProgram_trace {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B) :
    Trace (jointProgram B)
      (3 * Encoding.formulaBitLength F + 10 * (countWord (SAT.count F)).length + 13)
      (initial (jointProgram B) (Encoding.encodeCNF F))
      ((finalState (countWord (SAT.count F))).withPC none) := by
  have ht := compiled_halt_trace (jointCommand_eval F hn) ABI.countStack ABI.answerStack
  change Trace (jointProgram B)
    (3 * Encoding.formulaBitLength F + 10 * (countWord (SAT.count F)).length + 13)
    ((countState (Encoding.encodeCNF F)).withPC (some (jointProgram B).entry))
    ((finalState (countWord (SAT.count F))).withPC none)
  simpa only [jointProgram, Nat.add_assoc] using ht

theorem finalState_count (word : List Bool) :
    (finalState word).stacks ABI.countStack = word := by
  have h := Native.positivityResult_count Native.positivityPorts ABI.answerStack
    (countState word)
    (by simp [countState, StructuredProgram.ioState, Native.positivityPorts,
      ABI.countStack, ABI.positivityScratch]) ABI.countStack_ne_answerStack
  simpa [finalState, Native.positivityPorts, countState, StructuredProgram.ioState] using h

theorem finalState_answer (word : List Bool) :
    (finalState word).stacks ABI.answerStack =
      [decide (0 < BinaryArithmetic.toNat word)] := by
  rw [finalState, Native.positivityResult_answer]
  · simp [countState, StructuredProgram.ioState, Native.positivityPorts]
  · simp [countState, StructuredProgram.ioState, Native.positivityPorts,
      ABI.countStack, ABI.positivityScratch]
  · simp [countState, StructuredProgram.ioState, ABI.countStack, ABI.answerStack]

/-- Both physical outputs, real primitive time, and every-prefix visited space
are established for the same guarded execution. This theorem covers only the
fixed finite exceptional range; its constants may depend on the cutoff. -/
theorem primitive_trace {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B) :
    ∃ time : ℕ, ∃ final : LocatedCfg (GuardedCompiler.primitive (jointProgram B)),
      Computation.Trace (locatedStep (GuardedCompiler.primitive (jointProgram B))) time
        (locatedInit (GuardedCompiler.primitive (jointProgram B)) (Encoding.encodeCNF F))
        final ∧
      final.config.state = .inl (decide (0 < SAT.count F)) ∧
      final.config.tapes ABI.countStack =
        Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
      final.config.tapes ABI.answerStack =
        Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
      time ≤ 7 * (3 * Encoding.formulaBitLength F + 10 * B + 23) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (GuardedCompiler.primitive (jointProgram B)))
          prefixSteps
          (locatedInit (GuardedCompiler.primitive (jointProgram B)) (Encoding.encodeCNF F))
          intermediate →
        visitedSpace intermediate ≤
          1220 * (5 * Encoding.formulaBitLength F + 10 * B + 38) := by
  have hw : (countWord (SAT.count F)).length ≤ B + 1 :=
    (countWord_count_length F).trans (Nat.add_le_add_right hn 1)
  have hs := StructuredSpace.local_stack_bound (jointProgram B)
    (steps := 3 * Encoding.formulaBitLength F +
      10 * (countWord (SAT.count F)).length + 13)
    (show BitProgram.dataBits (initial (jointProgram B) (Encoding.encodeCNF F)) ≤
      (Encoding.encodeCNF F).length by simp)
  have ha : ((finalState (countWord (SAT.count F))).withPC
      (none : Option (Fin (size (jointCommand B) + 1)))).stacks
      (jointProgram B).outputStack = [decide (0 < SAT.count F)] := by
    simpa only [jointProgram, compiled, StructuredProgram.State.withPC, countWord_toNat]
      using finalState_answer (countWord (SAT.count F))
  obtain ⟨time, ht, final, hrun, hhalt, hcount, hanswer, hspace⟩ :=
    CompileSpace.compile_word_answer_space (jointProgram B) ABI.countStack
      (jointProgram_trace F hn) rfl (finalState_count _) ha hs
  refine ⟨time, final, hrun, hhalt, hcount, hanswer, ?_, ?_⟩
  · omega
  · intro prefixSteps intermediate hprefix htrace
    apply (hspace prefixSteps intermediate hprefix htrace).trans
    apply Nat.mul_le_mul_left 1220
    change (Encoding.formulaBitLength F +
      (3 * Encoding.formulaBitLength F + 10 * (countWord (SAT.count F)).length + 13)) +
        Encoding.formulaBitLength F + 15 ≤ _
    omega

def timeCoefficient (B : ℕ) : ℕ := 7 * (10 * B + 26)

def spaceCoefficient (B : ℕ) : ℕ := 1220 * (10 * B + 43)

/-- Explicit fixed positive coefficients give linear input-length resources
for the bounded-variable counter, including the actual SAT positivity output. -/
theorem polynomial_trace {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B) :
    ∃ time : ℕ, ∃ final : LocatedCfg (GuardedCompiler.primitive (jointProgram B)),
      Computation.Trace (locatedStep (GuardedCompiler.primitive (jointProgram B))) time
        (locatedInit (GuardedCompiler.primitive (jointProgram B)) (Encoding.encodeCNF F))
        final ∧
      final.config.state = .inl (decide (0 < SAT.count F)) ∧
      final.config.tapes ABI.countStack =
        Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
      final.config.tapes ABI.answerStack =
        Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
      (decide (0 < SAT.count F) = true ↔ SAT.Satisfiable F) ∧
      time ≤ timeCoefficient B * (Encoding.formulaBitLength F + 1) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (GuardedCompiler.primitive (jointProgram B)))
          prefixSteps
          (locatedInit (GuardedCompiler.primitive (jointProgram B)) (Encoding.encodeCNF F))
          intermediate →
        visitedSpace intermediate ≤ spaceCoefficient B * (Encoding.formulaBitLength F + 1) := by
  obtain ⟨time, final, htrace, hhalt, hcount, hanswer, htime, hspace⟩ := primitive_trace F hn
  refine ⟨time, final, htrace, hhalt, hcount, hanswer, ?_, ?_, ?_⟩
  · simp [SAT.count_pos_iff]
  · apply htime.trans
    unfold timeCoefficient
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left 7
    have h := Nat.mul_le_mul_right (Encoding.formulaBitLength F)
      (show 3 ≤ 10 * B + 26 by omega)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · intro prefixSteps intermediate hprefix hprefixTrace
    apply (hspace prefixSteps intermediate hprefix hprefixTrace).trans
    unfold spaceCoefficient
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left 1220
    have h := Nat.mul_le_mul_right (Encoding.formulaBitLength F)
      (show 5 ≤ 10 * B + 43 by omega)
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- Only the scanner's two registers are reset; all dispatcher tapes survive. -/
def resetScannerRegs (regs : Fin 80 → Bool) : Fin 80 → Bool :=
  Function.update (Function.update regs 0 false) 1 false

def resetScanner : Cmd 80 1220 :=
  .base (.seq (.atom (.set 0 false)) (.atom (.set 1 false)))

def scannerState (a : State 80 1220) (word : List Bool) : State 80 1220 :=
  ⟨resetScannerRegs a.regs, Function.update a.stacks ABI.countStack word⟩

theorem resetScanner_eval (a : State 80 1220) :
    Eval resetScanner 2 a ⟨resetScannerRegs a.regs, a.stacks⟩ :=
  .base (.seq (.atom _ _) (.atom _ _))

noncomputable def framedCountCommand (B : ℕ) : Cmd 80 1220 :=
  .seq resetScanner (.call (ProgramLinking.liftProgram (countProgram B)
    (Fin.castAdd 78) (fun _ : Fin 1 => ABI.countStack)))

/-- The finite scanner is callable after preprocessing, with arbitrary framed
registers and stacks. Its own initial registers are established by real steps. -/
theorem framedCountCommand_eval {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B)
    (a : State 80 1220) (hinput : a.stacks ABI.countStack = Encoding.encodeCNF F) :
    Eval (framedCountCommand B)
      (3 * Encoding.formulaBitLength F + 2 * (countWord (SAT.count F)).length + 6)
      a (scannerState a (countWord (SAT.count F))) := by
  have hs : Function.Injective (fun _ : Fin 1 => ABI.countStack) :=
    fun _ _ _ => Subsingleton.elim _ _
  let frame : State 80 1220 := ⟨resetScannerRegs a.regs, a.stacks⟩
  have he (word : List Bool) :
      embedState (Fin.castAdd 78) (fun _ : Fin 1 => ABI.countStack) frame
        (StructuredProgram.ioState 0 word) = scannerState a word := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 2 78) hs
    · intro i
      fin_cases i <;> simp [scannerState, resetScannerRegs]
    · intro i hi
      rfl
    · intro i
      simp [scannerState, Fin.eq_zero i]
    · intro i hi
      have hne : i ≠ ABI.countStack := fun h => hi ⟨0, h.symm⟩
      simp [scannerState, frame, hne]
  have hc := eval_call_lifted (countProgram B) (Fin.castAdd 78)
    (fun _ : Fin 1 => ABI.countStack) frame (Fin.castAdd_injective 2 78) hs
    (a := StructuredProgram.ioState 0 (Encoding.encodeCNF F))
    (b := StructuredProgram.ioState 0 (countWord (SAT.count F)))
    (canonical_count_trace F hn)
  rw [he, he] at hc
  have hi : scannerState a (Encoding.encodeCNF F) = frame := by
    simp [scannerState, ← hinput, frame]
  rw [hi] at hc
  have ht := (resetScanner_eval a).seq hc
  convert ht using 1
  all_goals try rfl
  all_goals omega

noncomputable def framedCommand (B : ℕ) : Cmd 80 1220 :=
  .seq (framedCountCommand B) Native.answerCommand

noncomputable def framedProgram (B : ℕ) :=
  compiled (framedCommand B) ABI.countStack ABI.answerStack

noncomputable def framedResult (a : State 80 1220) (word : List Bool) : State 80 1220 :=
  Native.answerResult (scannerState a word)

theorem framedCommand_eval {B n : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B)
    (a : State 80 1220) (hinput : a.stacks ABI.countStack = Encoding.encodeCNF F) :
    Eval (framedCommand B)
      (3 * Encoding.formulaBitLength F + 10 * (countWord (SAT.count F)).length +
        2 * (a.stacks ABI.answerStack).length +
        2 * (a.stacks ABI.positivityScratch).length + 20)
      a (framedResult a (countWord (SAT.count F))) := by
  have ht := (framedCountCommand_eval F hn a hinput).seq
    (Native.answerCommand_eval (scannerState a (countWord (SAT.count F))))
  convert ht using 1
  all_goals try rfl
  simp only [Native.answerSteps, scannerState, Function.update_self,
    Function.update_of_ne (show ABI.answerStack ≠ ABI.countStack by decide),
    Function.update_of_ne (show ABI.positivityScratch ≠ ABI.countStack by decide)]
  omega

theorem framedResult_count (a : State 80 1220) (word : List Bool) :
    (framedResult a word).stacks ABI.countStack = word := by
  simp only [framedResult, Native.answerResult_count, scannerState, Function.update_self]

theorem framedResult_answer (a : State 80 1220) (word : List Bool) :
    (framedResult a word).stacks ABI.answerStack =
      [decide (0 < BinaryArithmetic.toNat word)] := by
  simp only [framedResult, Native.answerResult_answer, scannerState, Function.update_self]

theorem framedResult_frame (a : State 80 1220) (word : List Bool) (i : Fin 1220)
    (hc : i ≠ ABI.countStack) (ha : i ≠ ABI.answerStack)
    (hs : i ≠ ABI.positivityScratch) :
    (framedResult a word).stacks i = a.stacks i := by
  rw [framedResult, Native.answerResult,
    Native.positivityResult_stacks _ _ _ (Native.answerReady_scratch _)]
  simp [ha, hs, hc, Native.answerReady, Native.clearOutputState, scannerState]

/-- Source execution and every-prefix stack space for the actual framed call.
The bound includes every retained dispatcher stack, including old answer data. -/
theorem framedProgram_trace {B n D : ℕ} (F : SAT.CNF (Fin n)) (hn : n ≤ B)
    (a : State 80 1220) (hinput : a.stacks ABI.countStack = Encoding.encodeCNF F)
    (hframe : ∀ i, (a.stacks i).length ≤ D) :
    ∃ steps,
      Trace (framedProgram B) steps (a.withPC (some (framedProgram B).entry))
        ((framedResult a (countWord (SAT.count F))).withPC none) ∧
      steps ≤ 3 * Encoding.formulaBitLength F + 10 * B + 4 * D + 31 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (framedProgram B) prefixSteps
          (a.withPC (some (framedProgram B).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          1224 * D + 3 * Encoding.formulaBitLength F + 10 * B + 31 := by
  have ht := compiled_halt_trace (framedCommand_eval F hn a hinput)
    ABI.countStack ABI.answerStack
  have hw := (countWord_count_length F).trans (Nat.add_le_add_right hn 1)
  have ha := hframe ABI.answerStack
  have hs := hframe ABI.positivityScratch
  have hsize : BitProgram.dataBits (a.withPC (some (framedProgram B).entry)) ≤
      1220 * D := by
    change ∑ i : Fin 1220, (a.stacks i).length ≤ _
    calc
      _ ≤ ∑ _i : Fin 1220, D := Finset.sum_le_sum (fun i _ => hframe i)
      _ = _ := by simp
  refine ⟨_, ht, ?_, ?_⟩
  · omega
  · intro prefixSteps intermediate hprefix htrace i
    have h := StructuredSpace.local_stack_bound (framedProgram B) hsize
      prefixSteps intermediate hprefix htrace i
    omega

/-- Finite saturated control for the fixed exceptional cutoff; no numeric
cutoff is stored in an input-dependent runtime array. -/
def cutoffNext (B : ℕ) (q : Fin (B + 2)) (bit : Bool) : Fin (B + 2) :=
  ⟨min (B + 1) (q.val + if bit then 1 else 0), by omega⟩

def cutoffOut (B : ℕ) (q : Fin (B + 2)) : List Bool := [decide (q.val ≤ B)]

def cutoffScanner (B : ℕ) :=
  Scanner.program 1 (⟨0, by omega⟩ : Fin (B + 2)) (cutoffNext B) (cutoffOut B)
    (by intro q; rfl)

theorem cutoff_fold_replicate (B n : ℕ) (q : Fin (B + 2)) :
    ((List.replicate n true).foldl (cutoffNext B) q).val = min (B + 1) (q.val + n) := by
  induction n generalizing q with
  | zero => simp; omega
  | succ n ih =>
    simp only [List.replicate_succ, List.foldl_cons, ih, cutoffNext, ite_true]
    omega

theorem cutoff_fold_header (B n : ℕ) :
    cutoffOut B ((Encoding.encodeNat n).foldl (cutoffNext B) ⟨0, by omega⟩) =
      [decide (n ≤ B)] := by
  have h := cutoff_fold_replicate B n (⟨0, by omega⟩ : Fin (B + 2))
  simp only [Encoding.encodeNat, List.foldl_append, List.foldl_cons, List.foldl_nil,
    cutoffOut, cutoffNext, Bool.false_eq_true, ite_false, Nat.add_zero]
  simp only [Nat.zero_add] at h
  rw [h]
  have he : min (B + 1) (min (B + 1) n) ≤ B ↔ n ≤ B := by omega
  simp only [he]

theorem cutoffScanner_trace (B n : ℕ) (r : Fin 2 → Bool) :
    Trace (cutoffScanner B) (3 * (Encoding.encodeNat n).length + 6)
      ((⟨r, fun _ => Encoding.encodeNat n⟩ : State 2 1).withPC
        (some (cutoffScanner B).entry))
      ((StructuredProgram.ioState 0 [decide (n ≤ B)]).withPC none) := by
  have hr : Scanner.regs (r 0) (r 1) = r := by
    funext i; fin_cases i <;> rfl
  have h := Scanner.trace 1 (⟨0, by omega⟩ : Fin (B + 2)) (cutoffNext B)
    (cutoffOut B) (by intro q; rfl) ⟨0, by omega⟩ (Encoding.encodeNat n) (r 0) (r 1)
  rw [cutoff_fold_header] at h
  simpa [cutoffScanner, Scanner.cfg, Scanner.program, hr, terminal,
    StructuredProgram.ioState, StructuredProgram.State.withPC] using h

def cutoffRegs : Fin 2 ↪ Fin 80 where
  toFun := ![75, 76]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def cutoffPrepare : Cmd 80 1220 :=
  .seq (Native.clearOutput 270) (Native.clearOutput 271)

def cutoffPrepared (a : State 80 1220) : State 80 1220 :=
  Native.clearOutputState 271 (Native.clearOutputState 270 a)

def cutoffCopied (a : State 80 1220) : State 80 1220 :=
  Native.copiedWord 258 270 (cutoffPrepared a)

noncomputable def cutoffScanned (a : State 80 1220) (flag : Bool) : State 80 1220 :=
  embedState cutoffRegs (fun _ : Fin 1 => (270 : Fin 1220)) (cutoffCopied a)
    (StructuredProgram.ioState 0 [flag])

noncomputable def cutoffResult (a : State 80 1220) (flag : Bool) : State 80 1220 :=
  (StructuredProgram.Atom.pop 270 75 76).eval (cutoffScanned a flag)

noncomputable def cutoffCommand (B : ℕ) : Cmd 80 1220 :=
  .seq cutoffPrepare (.seq (Native.copyWord 258 270 271)
    (.seq (.call (ProgramLinking.liftProgram (cutoffScanner B) cutoffRegs
      (fun _ : Fin 1 => (270 : Fin 1220)))) (.base (.atom (.pop 270 75 76)))))

theorem cutoffPrepare_eval (a : State 80 1220) :
    Eval cutoffPrepare (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 6)
      a (cutoffPrepared a) := by
  have h := (Native.clearOutput_eval 270 a).seq
    (Native.clearOutput_eval 271 (Native.clearOutputState 270 a))
  convert h using 1
  all_goals try rfl
  simp [Native.clearOutputState]
  omega

theorem cutoffCommand_eval (B n : ℕ) (a : State 80 1220)
    (hn : a.stacks 258 = Encoding.encodeNat n) :
    Eval (cutoffCommand B)
      (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 10 * n + 28)
      a (cutoffResult a (decide (n ≤ B))) := by
  have hcopy := Native.copyWord_eval 258 270 271 (cutoffPrepared a)
    (by decide) (by decide) (by decide)
    (by simp [cutoffPrepared, Native.clearOutputState])
  have hs : Function.Injective (fun _ : Fin 1 => (270 : Fin 1220)) :=
    fun _ _ _ => Subsingleton.elim _ _
  have hp : projectState cutoffRegs (fun _ : Fin 1 => (270 : Fin 1220)) (cutoffCopied a) =
      (⟨(cutoffCopied a).regs ∘ cutoffRegs, fun _ => Encoding.encodeNat n⟩ : State 2 1) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      simp [projectState, cutoffCopied, Native.copiedWord, StackRoutines.copyStacks,
        cutoffPrepared, Native.clearOutputState, hn]
  have ht := cutoffScanner_trace B n ((cutoffCopied a).regs ∘ cutoffRegs)
  rw [← hp] at ht
  have hscan := eval_call_from_state (cutoffScanner B) cutoffRegs
    (fun _ : Fin 1 => (270 : Fin 1220)) (cutoffCopied a) cutoffRegs.injective hs ht
  have hpop := Eval.base (StructuredProgram.Eval.atom (.pop (270 : Fin 1220) 75 76)
    (cutoffScanned a (decide (n ≤ B))))
  have h := (cutoffPrepare_eval a).seq (hcopy.seq (hscan.seq hpop))
  convert h using 1
  all_goals try rfl
  simp only [cutoffPrepared, Native.clearOutputState, Function.update_of_ne
    (show (258 : Fin 1220) ≠ 271 by decide), Function.update_of_ne
    (show (258 : Fin 1220) ≠ 270 by decide), hn, Encoding.length_encodeNat]
  omega

theorem cutoffScanned_word (a : State 80 1220) (flag : Bool) :
    (cutoffScanned a flag).stacks 270 = [flag] :=
  embedState_stack _ _ _ _ (fun _ _ _ => Subsingleton.elim _ _) 0

theorem cutoffScanned_frame (a : State 80 1220) (flag : Bool) (i : Fin 1220)
    (hi : i ≠ 270) : (cutoffScanned a flag).stacks i = (cutoffCopied a).stacks i :=
  embedState_stack_frame _ _ _ _ i (by rintro ⟨j, hj⟩; exact hi hj.symm)

@[simp] theorem cutoffResult_flag (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).regs 75 = flag := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,
    execInstr, cutoffScanned_word, readRegs]

@[simp] theorem cutoffResult_work (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).stacks 270 = [] := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,
    execInstr, cutoffScanned_word]

@[simp] theorem cutoffResult_scratch (a : State 80 1220) (flag : Bool) :
    (cutoffResult a flag).stacks 271 = [] := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    cutoffScanned_frame a flag 271 (by decide), cutoffCopied, Native.copiedWord,
    StackRoutines.copyStacks, cutoffPrepared, Native.clearOutputState]

theorem cutoffResult_frame (a : State 80 1220) (flag : Bool) (i : Fin 1220)
    (hw : i ≠ 270) (hs : i ≠ 271) : (cutoffResult a flag).stacks i = a.stacks i := by
  simp [cutoffResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, hw,
    cutoffScanned_frame a flag i hw, cutoffCopied, Native.copiedWord,
    StackRoutines.copyStacks, cutoffPrepared, Native.clearOutputState, hs]

theorem cutoffResult_bound (a : State 80 1220) (flag : Bool) {D : ℕ}
    (hframe : ∀ i, (a.stacks i).length ≤ D) :
    ∀ i, ((cutoffResult a flag).stacks i).length ≤ D := by
  intro i
  by_cases hw : i = 270
  · subst i; simp
  · by_cases hs : i = 271
    · subst i; simp
    · rw [cutoffResult_frame a flag i hw hs]
      exact hframe i

noncomputable def cutoffProgram (B : ℕ) := compiled (cutoffCommand B) 258 270

theorem cutoffProgram_trace (B n : ℕ) (a : State 80 1220)
    (hn : a.stacks 258 = Encoding.encodeNat n)
    {D : ℕ} (hframe : ∀ i, (a.stacks i).length ≤ D) :
    ∃ steps,
      Trace (cutoffProgram B) steps (a.withPC (some (cutoffProgram B).entry))
        ((cutoffResult a (decide (n ≤ B))).withPC none) ∧
      steps ≤ 4 * D + 10 * n + 29 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (cutoffProgram B) prefixSteps
          (a.withPC (some (cutoffProgram B).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 1224 * D + 10 * n + 29 := by
  have hsize : dataBits (a.withPC (some (cutoffProgram B).entry)) ≤ 1220 * D := by
    change ∑ i : Fin 1220, (a.stacks i).length ≤ _
    calc
      _ ≤ ∑ _i : Fin 1220, D := Finset.sum_le_sum (fun i _ => hframe i)
      _ = _ := by simp
  have h270 := hframe 270
  have h271 := hframe 271
  refine ⟨_, compiled_halt_trace (cutoffCommand_eval B n a hn) 258 270, by omega, ?_⟩
  intro prefixSteps intermediate hprefix htrace i
  have h := StructuredSpace.local_stack_bound (cutoffProgram B) hsize
    prefixSteps intermediate hprefix htrace i
  omega

/-- The small/large choice is made by the actual cutoff flag. The large branch
is a finite command selected before the input; no execution service is assumed. -/
noncomputable def dispatchCommand (B : ℕ) (large : Cmd 80 1220) : Cmd 80 1220 :=
  .seq (cutoffCommand B) (.ite 75 (framedCommand B) large)

theorem dispatch_small_eval {B n : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (hn : n ≤ B) (a : State 80 1220)
    (hheader : a.stacks 258 = Encoding.encodeNat n)
    (hinput : a.stacks ABI.countStack = Encoding.encodeCNF F) :
    Eval (dispatchCommand B large)
      (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 10 * n +
        3 * Encoding.formulaBitLength F + 10 * (countWord (SAT.count F)).length +
        2 * (a.stacks ABI.answerStack).length +
        2 * (a.stacks ABI.positivityScratch).length + 49)
      a (framedResult (cutoffResult a true) (countWord (SAT.count F))) := by
  have hcut := cutoffCommand_eval B n a hheader
  simp only [decide_eq_true hn] at hcut
  have hc := framedCommand_eval F hn (cutoffResult a true)
    ((cutoffResult_frame a true ABI.countStack (by decide) (by decide)).trans hinput)
  have ht : Eval (dispatchCommand B large) _ a
      (framedResult (cutoffResult a true) (countWord (SAT.count F))) :=
    hcut.seq (Eval.ite_true (cutoffResult_flag a true) hc)
  convert ht using 1
  rw [cutoffResult_frame a true ABI.answerStack (by decide) (by decide),
    cutoffResult_frame a true ABI.positivityScratch (by decide) (by decide)]
  omega

noncomputable def dispatchProgram (B : ℕ) (large : Cmd 80 1220) :=
  compiled (dispatchCommand B large) ABI.countStack ABI.answerStack

theorem dispatch_small_trace {B n D : ℕ} (large : Cmd 80 1220)
    (F : SAT.CNF (Fin n)) (hn : n ≤ B) (a : State 80 1220)
    (hheader : a.stacks 258 = Encoding.encodeNat n)
    (hinput : a.stacks ABI.countStack = Encoding.encodeCNF F)
    (hframe : ∀ i, (a.stacks i).length ≤ D) :
    ∃ steps,
      Trace (dispatchProgram B large) steps
        (a.withPC (some (dispatchProgram B large).entry))
        ((framedResult (cutoffResult a true) (countWord (SAT.count F))).withPC none) ∧
      steps ≤ 8 * D + 20 * B + 3 * Encoding.formulaBitLength F + 60 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (dispatchProgram B large) prefixSteps
          (a.withPC (some (dispatchProgram B large).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          1228 * D + 20 * B + 3 * Encoding.formulaBitLength F + 60 := by
  have hsize : dataBits (a.withPC (some (dispatchProgram B large).entry)) ≤ 1220 * D := by
    change ∑ i : Fin 1220, (a.stacks i).length ≤ _
    calc
      _ ≤ ∑ _i : Fin 1220, D := Finset.sum_le_sum (fun i _ => hframe i)
      _ = _ := by simp
  have h270 := hframe 270
  have h271 := hframe 271
  have hanswer := hframe ABI.answerStack
  have hscratch := hframe ABI.positivityScratch
  have hword := (countWord_count_length F).trans (Nat.add_le_add_right hn 1)
  refine ⟨_, compiled_halt_trace (dispatch_small_eval large F hn a hheader hinput)
    ABI.countStack ABI.answerStack, by omega, ?_⟩
  intro prefixSteps intermediate hprefix htrace i
  have h := StructuredSpace.local_stack_bound (dispatchProgram B large) hsize
    prefixSteps intermediate hprefix htrace i
  omega


/-- The complementary branch uses the same actual cutoff scan and preserves
its input frame before entering the fixed large-input command. -/
theorem dispatch_large_eval {B n steps : ℕ} (large : Cmd 80 1220)
    (hn : B < n) (a b : State 80 1220)
    (hheader : a.stacks 258 = Encoding.encodeNat n)
    (he : Eval large steps (cutoffResult a false) b) :
    Eval (dispatchCommand B large)
      (2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 10 * n + 29 + steps)
      a b := by
  have hcut := cutoffCommand_eval B n a hheader
  have hn' : ¬ n ≤ B := by omega
  simp only [decide_eq_false hn'] at hcut
  have whole := hcut.seq (he.ite_false (yes := framedCommand B) (cutoffResult_flag a false))
  convert whole using 1
  all_goals try rfl
  all_goals omega

/-- A local prefix bound for the dispatcher composes with the proved prefix
bound of its actual large command, independently of the large running time. -/
theorem dispatch_large_space {B n steps D bound : ℕ} (large : Cmd 80 1220)
    (hn : B < n) (a b : State 80 1220)
    (hheader : a.stacks 258 = Encoding.encodeNat n)
    (hframe : ∀ i, (a.stacks i).length ≤ D)
    (hbudget : 1224 * D + 10 * n + 28 ≤ bound)
    (he : Eval large steps (cutoffResult a false) b)
    (hlarge : ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled large 256 256) prefixSteps
        ((cutoffResult a false).withPC (some (compiled large 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound) :
    ∀ prefixSteps c,
      prefixSteps ≤ 2 * (a.stacks 270).length + 2 * (a.stacks 271).length +
        10 * n + 29 + steps →
      Trace (compiled (dispatchCommand B large) 256 256) prefixSteps
        (a.withPC (some (compiled (dispatchCommand B large) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  have hcut := cutoffCommand_eval B n a hheader
  have hn' : ¬ n ≤ B := by omega
  simp only [decide_eq_false hn'] at hcut
  have hsize : dataBits
      (a.withPC (some (compiled (cutoffCommand B) 256 256).entry)) ≤ 1220 * D := by
    change ∑ i : Fin 1220, (a.stacks i).length ≤ _
    calc
      _ ≤ ∑ _i : Fin 1220, D := Finset.sum_le_sum (fun i _ => hframe i)
      _ = _ := by simp
  have hcutspace : ∀ prefixSteps c,
      prefixSteps ≤ 2 * (a.stacks 270).length + 2 * (a.stacks 271).length + 10 * n + 28 →
      Trace (compiled (cutoffCommand B) 256 256) prefixSteps
        (a.withPC (some (compiled (cutoffCommand B) 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro prefixSteps c hp hc i
    have hg := StructuredSpace.local_stack_bound (compiled (cutoffCommand B) 256 256)
      hsize prefixSteps c hp hc i
    have h270 := hframe 270
    have h271 := hframe 271
    omega
  have hbranch := StructuredSpace.conditional_false_stack_bound
    (cutoffResult_flag a false) he 256 256 hlarge
    (compiled (.ite 75 (framedCommand B) large) 256 256)
    (siteAddress (.ite 75 (framedCommand B) large))
    (exitAddress (.ite 75 (framedCommand B) large))
    (compiled_site (.ite 75 (framedCommand B) large) 256 256)
  have whole := StructuredSpace.sequence_stack_bound hcut
    (he.ite_false (yes := framedCommand B) (cutoffResult_flag a false)) 256 256 hcutspace hbranch
    (compiled (dispatchCommand B large) 256 256) (siteAddress (dispatchCommand B large))
    (exitAddress (dispatchCommand B large)) (compiled_site (dispatchCommand B large) 256 256)
  intro prefixSteps c hp hc i
  exact whole prefixSteps c (by omega) hc i


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback
