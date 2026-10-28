import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.ParameterOrder

namespace OAI.Algorithms

/-!
# Fixed finite programs and measured expansion of TM2 statements

This module expands TM2's finite statement blocks into actual one-constructor
stack transitions.  The execution theorem counts those transitions.  It does
not identify a stack operation with a primitive binary tape operation; that
additional encoding is a separate compiler layer.
-/

namespace SubexponentialSAT.FixedParameters

open SubexponentialSAT.Computation
open Turing.TM2

instance labelFintype (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
instance variableFintype (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- The number of constructor nodes in a finite statement. -/
def statementSize {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Stmt Γ Λ σ → ℕ
  | .push _ _ q => statementSize q + 1
  | .peek _ _ q => statementSize q + 1
  | .pop _ _ q => statementSize q + 1
  | .load _ q => statementSize q + 1
  | .branch _ q₁ q₂ => statementSize q₁ + statementSize q₂ + 1
  | .goto _ => 1
  | .halt => 1

theorem statementSize_pos {K : Type} {Γ : K → Type} {Λ σ : Type}
    (q : Stmt Γ Λ σ) : 0 < statementSize q := by
  cases q <;> simp [statementSize]

/-- A configuration during expansion of a source statement. -/
structure MicroCfg (tm : Turing.FinTM2) where
  code : Option (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
  var : tm.σ
  stk : ∀ k, List (tm.Γ k)

/-- Source block boundaries are represented by their next statement. -/
def embed (tm : Turing.FinTM2) (c : tm.Cfg) : MicroCfg tm :=
  ⟨c.l.map tm.m, c.var, c.stk⟩

/-- One transition executes one constructor, and at most one stack operation. -/
def microStep (tm : Turing.FinTM2) : MicroCfg tm → Option (MicroCfg tm)
  | ⟨none, _, _⟩ => none
  | ⟨some (.push k f q), v, S⟩ =>
      some ⟨some q, v, Function.update S k (f v :: S k)⟩
  | ⟨some (.peek k f q), v, S⟩ =>
      some ⟨some q, f v (S k).head?, S⟩
  | ⟨some (.pop k f q), v, S⟩ =>
      some ⟨some q, f v (S k).head?, Function.update S k (S k).tail⟩
  | ⟨some (.load f q), v, S⟩ => some ⟨some q, f v, S⟩
  | ⟨some (.branch f q₁ q₂), v, S⟩ =>
      some ⟨some (if f v then q₁ else q₂), v, S⟩
  | ⟨some (.goto f), v, S⟩ => some ⟨some (tm.m (f v)), v, S⟩
  | ⟨some .halt, v, S⟩ => some ⟨none, v, S⟩

private theorem one_step {α : Type} {step : α → Option α} {a b : α}
    (h : step a = some b) : RunsIn step 1 a b :=
  ⟨1, le_rfl, Trace.cons h (Trace.refl b)⟩

/-- Every source statement has a measured, finite expansion into microsteps. -/
theorem statement_micro_execution (tm : Turing.FinTM2) (q : tm.Stmt)
    (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    RunsIn (microStep tm) (statementSize q) ⟨some q, v, S⟩
      (embed tm (stepAux q v S)) := by
  induction q generalizing v S with
  | push k f q ih =>
      have h := (one_step (step := microStep tm)
        (a := ⟨some (.push k f q), v, S⟩) rfl).trans
          (ih v (Function.update S k (f v :: S k)))
      simpa [statementSize, stepAux, Nat.add_comm] using h
  | peek k f q ih =>
      have h := (one_step (step := microStep tm)
        (a := ⟨some (.peek k f q), v, S⟩) rfl).trans
          (ih (f v (S k).head?) S)
      simpa [statementSize, stepAux, Nat.add_comm] using h
  | pop k f q ih =>
      have h := (one_step (step := microStep tm)
        (a := ⟨some (.pop k f q), v, S⟩) rfl).trans
          (ih (f v (S k).head?) (Function.update S k (S k).tail))
      simpa [statementSize, stepAux, Nat.add_comm] using h
  | load f q ih =>
      have h := (one_step (step := microStep tm)
        (a := ⟨some (.load f q), v, S⟩) rfl).trans (ih (f v) S)
      simpa [statementSize, stepAux, Nat.add_comm] using h
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases hf : f v with
      | false =>
          have h := (one_step (step := microStep tm)
            (a := ⟨some (.branch f q₁ q₂), v, S⟩)
            (by simp [microStep, hf])).trans (ih₂ v S)
          have hle : 1 + statementSize q₂ ≤ statementSize (.branch f q₁ q₂) := by
            simp only [statementSize]
            omega
          simpa [stepAux, hf] using h.mono hle
      | true =>
          have h := (one_step (step := microStep tm)
            (a := ⟨some (.branch f q₁ q₂), v, S⟩)
            (by simp [microStep, hf])).trans (ih₁ v S)
          have hle : 1 + statementSize q₁ ≤ statementSize (.branch f q₁ q₂) := by
            simp only [statementSize]
            omega
          simpa [stepAux, hf] using h.mono hle
  | goto f => exact one_step rfl
  | halt => exact one_step rfl

/-- The largest source block is fixed by the machine, not by its input. -/
def blockOverhead (tm : Turing.FinTM2) : ℕ :=
  (Finset.univ : Finset tm.Λ).sup (fun l => statementSize (tm.m l))

theorem statementSize_le_blockOverhead (tm : Turing.FinTM2) (l : tm.Λ) :
    statementSize (tm.m l) ≤ blockOverhead tm := by
  exact Finset.le_sup (f := fun l : tm.Λ => statementSize (tm.m l))
    (Finset.mem_univ l)

theorem blockOverhead_pos (tm : Turing.FinTM2) : 0 < blockOverhead tm :=
  lt_of_lt_of_le (statementSize_pos (tm.m tm.main))
    (statementSize_le_blockOverhead tm tm.main)

/-- The local compiler theorem is proved from the transition definitions. -/
theorem micro_simulation (tm : Turing.FinTM2) :
    BoundedSimulation tm.step (microStep tm)
      (fun a b => b = embed tm a) (blockOverhead tm) := by
  intro a a' b hb hs
  subst b
  rcases a with ⟨label, v, S⟩
  cases label with
  | none => simp [Turing.FinTM2.step, step] at hs
  | some l =>
      have heq : stepAux (tm.m l) v S = a' := by
        exact Option.some.inj hs
      subst a'
      refine ⟨embed tm (stepAux (tm.m l) v S), rfl, ?_⟩
      exact (statement_micro_execution tm (tm.m l) v S).mono
        (statementSize_le_blockOverhead tm l)

/-- A source run of t blocks expands to at most C_tm * t actual microsteps. -/
theorem micro_execution (tm : Turing.FinTM2) {a b : tm.Cfg} {time : ℕ}
    (h : RunsIn tm.step time a b) :
    RunsIn (microStep tm) (blockOverhead tm * time) (embed tm a) (embed tm b) := by
  obtain ⟨c, hc, hrun⟩ := simulate_runsIn (micro_simulation tm) h rfl
  simpa [hc] using hrun

/-- All microcode comes from a finite set of substatements of source blocks. -/
noncomputable def codeSet (tm : Turing.FinTM2) :
    Finset (Option (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)) :=
  stmts tm.m Finset.univ

theorem embed_code_mem (tm : Turing.FinTM2) (c : tm.Cfg) :
    (embed tm c).code ∈ codeSet tm := by
  classical
  rcases c with ⟨label, v, S⟩
  cases label with
  | none =>
      change none ∈ Finset.insertNone
        ((Finset.univ : Finset tm.Λ).biUnion fun q => stmts₁ (tm.m q))
      exact Finset.none_mem_insertNone
  | some l =>
      change some (tm.m l) ∈ codeSet tm
      rw [codeSet, stmts, Finset.some_mem_insertNone]
      exact Finset.mem_biUnion.mpr
        ⟨l, Finset.mem_univ l, (stmts₁_self : tm.m l ∈ stmts₁ (tm.m l))⟩

/-- Executing one constructor cannot introduce code outside the fixed program. -/
theorem microStep_code_mem (tm : Turing.FinTM2) {a b : MicroCfg tm}
    (ha : a.code ∈ codeSet tm) (hstep : microStep tm a = some b) :
    b.code ∈ codeSet tm := by
  classical
  rcases a with ⟨code, v, S⟩
  cases code with
  | none => simp [microStep] at hstep
  | some q =>
      cases q with
      | push k f q =>
          simp only [microStep, Option.some.injEq] at hstep
          subst b
          exact stmts_trans (by simp [stmts₁, stmts₁_self]) ha
      | peek k f q =>
          simp only [microStep, Option.some.injEq] at hstep
          subst b
          exact stmts_trans (by simp [stmts₁, stmts₁_self]) ha
      | pop k f q =>
          simp only [microStep, Option.some.injEq] at hstep
          subst b
          exact stmts_trans (by simp [stmts₁, stmts₁_self]) ha
      | load f q =>
          simp only [microStep, Option.some.injEq] at hstep
          subst b
          exact stmts_trans (by simp [stmts₁, stmts₁_self]) ha
      | branch f q₁ q₂ =>
          simp only [microStep, Option.some.injEq] at hstep
          subst b
          cases hf : f v <;>
            simp only [ Bool.false_eq_true, ↓reduceIte]
          · exact stmts_trans (by simp [stmts₁, stmts₁_self]) ha
          · exact stmts_trans (by simp [stmts₁, stmts₁_self]) ha
      | goto f =>
          simp only [microStep, Option.some.injEq] at hstep
          subst b
          exact embed_code_mem tm ⟨some (f v), v, S⟩
      | halt =>
          simp only [microStep, Option.some.injEq] at hstep
          subst b
          exact embed_code_mem tm ⟨none, v, S⟩

/-- Every state in an actual micro-execution retains fixed finite code. -/
theorem microTrace_code_mem (tm : Turing.FinTM2) {a b : MicroCfg tm} {time : ℕ}
    (h : Trace (microStep tm) time a b) (ha : a.code ∈ codeSet tm) :
    b.code ∈ codeSet tm := by
  induction h with
  | refl => exact ha
  | cons hs ht ih => exact ih (microStep_code_mem tm ha hs)

/-- The complete set of instruction pointers is finite for each fixed source. -/
def Control (tm : Turing.FinTM2) :=
  {q : Option (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) // q ∈ codeSet tm}

noncomputable instance controlFintype (tm : Turing.FinTM2) : Fintype (Control tm) := by
  unfold Control
  infer_instance

/-- A micro-configuration with its finite-code invariant built into the type. -/
def FiniteMicroCfg (tm : Turing.FinTM2) :=
  {c : MicroCfg tm // c.code ∈ codeSet tm}

/-- The finite portion of the compiled control: instruction and local variables. -/
def finiteControl (tm : Turing.FinTM2) (c : FiniteMicroCfg tm) : Control tm × tm.σ :=
  (⟨c.val.code, c.property⟩, c.val.var)

/-- Restricting the transition function requires no additional runtime operation. -/
def finiteMicroStep (tm : Turing.FinTM2) (a : FiniteMicroCfg tm) :
    Option (FiniteMicroCfg tm) :=
  match h : microStep tm a.val with
  | none => none
  | some b => some ⟨b, microStep_code_mem tm a.property h⟩

/-- The compiled initial and block-boundary configurations. -/
def finiteEmbed (tm : Turing.FinTM2) (a : tm.Cfg) : FiniteMicroCfg tm :=
  ⟨embed tm a, embed_code_mem tm a⟩

theorem finiteMicroStep_of_step (tm : Turing.FinTM2) {a b : FiniteMicroCfg tm}
    (h : microStep tm a.val = some b.val) : finiteMicroStep tm a = some b := by
  unfold finiteMicroStep
  split
  · rename_i heq
    rw [heq] at h
    contradiction
  · rename_i c heq
    have hc : c = b.val := Option.some.inj (heq.symm.trans h)
    subst c
    congr

/-- Erasing invariant proofs recovers exactly one stack microtransition. -/
theorem finiteMicroStep_forget (tm : Turing.FinTM2) (a : FiniteMicroCfg tm) :
    (finiteMicroStep tm a).map Subtype.val = microStep tm a.val := by
  unfold finiteMicroStep
  split
  · rename_i heq
    change none = microStep tm a.val
    exact heq.symm
  · rename_i b heq
    change some b = microStep tm a.val
    exact heq.symm

/-- Restriction to finite code preserves the exact number of actual steps. -/
theorem finiteTrace_of_microTrace (tm : Turing.FinTM2) {a b : MicroCfg tm} {time : ℕ}
    (h : Trace (microStep tm) time a b) :
    ∀ (ha : a.code ∈ codeSet tm) (hb : b.code ∈ codeSet tm),
      Trace (finiteMicroStep tm) time ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl a => intro ha hb; exact Trace.refl (⟨a, ha⟩ : FiniteMicroCfg tm)
  | @cons n a c b hs ht ih =>
      intro ha hb
      have hc := microStep_code_mem tm ha hs
      exact Trace.cons (finiteMicroStep_of_step tm (a := ⟨a, ha⟩) (b := ⟨c, hc⟩) hs)
        (ih hc hb)

/-- A concrete finite-control stack implementation of every measured macro-run. -/
theorem finite_micro_execution (tm : Turing.FinTM2) {a b : tm.Cfg} {time : ℕ}
    (h : RunsIn tm.step time a b) :
    RunsIn (finiteMicroStep tm) (blockOverhead tm * time)
      (finiteEmbed tm a) (finiteEmbed tm b) := by
  obtain ⟨steps, hsteps, htrace⟩ := micro_execution tm h
  exact ⟨steps, hsteps,
    finiteTrace_of_microTrace tm htrace (embed_code_mem tm a) (embed_code_mem tm b)⟩

/-- A successful finite TM2 output has an actual finite-control stack execution. -/
theorem outputs_finite_micro_execution (machine : BitMachine)
    {input output : List Bool} {time : ℕ}
    (h : machine.OutputsInTime input output time) :
    RunsIn (finiteMicroStep machine.tm) (blockOverhead machine.tm * time)
      (finiteEmbed machine.tm
        (Turing.initList machine.tm (input.map machine.inputAlphabet.symm)))
      (finiteEmbed machine.tm
        (Turing.haltList machine.tm (output.map machine.outputAlphabet.symm))) :=
  finite_micro_execution machine.tm
    ((machine.outputsInTime_iff_runsIn input output time).mp h)

/-- Multiplying an established running time by a fixed constant preserves the exponent. -/
theorem fixed_multiplier_bound {constant exponent : ℝ} (overhead degree L n time : ℕ)
    (h : (time : ℝ) ≤ runtimeBound constant degree exponent L n) :
    ((overhead * time : ℕ) : ℝ) ≤
      runtimeBound ((overhead : ℝ) * constant) degree exponent L n := by
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg overhead : (0 : ℝ) ≤ overhead)
  simpa only [Nat.cast_mul, runtimeBound, mul_assoc] using hm

/-- A fixed startup and fixed per-step overhead are absorbed by a fixed coefficient.
The execution bound being transformed must be supplied separately. -/
theorem fixed_startup_bound {constant exponent : ℝ} (startup overhead degree L n time : ℕ)
    (he : 0 ≤ exponent)
    (h : (time : ℝ) ≤ runtimeBound constant degree exponent L n) :
    ((startup + overhead * time : ℕ) : ℝ) ≤
      runtimeBound ((startup : ℝ) + (overhead : ℝ) * constant)
        degree exponent L n := by
  have hpoly : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ degree := by
    apply one_le_pow₀
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have hexp : (1 : ℝ) ≤ Real.rpow 2 (exponent * (n : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg he (Nat.cast_nonneg n))
  have hfactor : (1 : ℝ) ≤ ((L : ℝ) + 1) ^ degree *
      Real.rpow 2 (exponent * (n : ℝ)) := one_le_mul_of_one_le_of_one_le hpoly hexp
  have hs := mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg startup : (0 : ℝ) ≤ startup)
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg overhead : (0 : ℝ) ≤ overhead)
  simp only [runtimeBound] at hm ⊢
  push_cast
  nlinarith

/-- Fixing any finite table yields a genuinely primitive-recursive lookup.
This is a computability statement, not a constant-time bit-machine assertion. -/
theorem fixed_table_primrec {α β : Type} [Primcodable α] [Primcodable β]
    [Finite α] (table : α → β) : Primrec table :=
  Primrec.dom_finite table

/-- Hardcoded parameters remain computable without an input-dependent oracle. -/
theorem hardcoded_parameter_computable {α β : Type} [Primcodable α] [Primcodable β]
    (parameter : β) : Computable (fun _ : α => parameter) :=
  Computable.const parameter

/-- Any selected parameter can be hardcoded once its width is fixed. This alone
does not assert computability of the entire width-indexed family. -/
theorem selected_parameter_hardcoded (test : ℕ → ℕ → Bool)
    (h : ∀ k, ∃ N, ∀ m ≥ N, test k m = true) (k : ℕ) :
    Computable (fun _ : List Bool => ParameterOrder.parameterFamily test h k) :=
  Computable.const _

/-- Effective parameter tests give actual computable preprocessing of a
width/input pair; its output ignores the variable input word. -/
theorem uniform_parameter_preprocessing (test : ℕ → ℕ → Bool)
    (htest : Computable₂ test)
    (h : ∀ k, ∃ N, ∀ m ≥ N, test k m = true) :
    Computable (fun input : ℕ × List Bool =>
      ParameterOrder.parameterFamily test h input.1) :=
  (ParameterOrder.computable_parameterFamily test htest h).comp Computable.fst


open SubexponentialSAT.Computation
open Turing

/-- A two-tape primitive program which writes a fixed word on work tape 1. -/
def wordWriter (word : List Bool) : PrimitiveMachine where
  tapeCount := 2
  stateCount := 2 * word.length + 1
  inputTape := 0
  start := ⟨0, by omega⟩
  scan _ := 1
  transition q _ :=
    if h : q.val < 2 * word.length then
      .inr (⟨q.val + 1, by omega⟩,
        if q.val % 2 = 0 then .write word[q.val / 2]?
        else .move .right)
    else .inl false

/-- Configuration before writing symbol i, or at the end when i=length. -/
def writerCfg (word : List Bool) (i : ℕ) (hi : i ≤ word.length)
    (tapes : Fin 2 → Tape (Option Bool)) : (wordWriter word).Cfg :=
  ⟨.inr ⟨2 * i, by dsimp [wordWriter]; omega⟩, tapes⟩

/-- One indexed symbol is written, and the work head advances one cell. -/
def writeIndex (word : List Bool) (i : ℕ)
    (tapes : Fin 2 → Tape (Option Bool)) : Fin 2 → Tape (Option Bool) :=
  Function.update tapes 1 (((tapes 1).write word[i]?).move .right)

theorem writer_pair (word : List Bool) (i : ℕ) (hi : i < word.length)
    (tapes : Fin 2 → Tape (Option Bool)) :
    Trace (wordWriter word).step 2 (writerCfg word i hi.le tapes)
      (writerCfg word (i + 1) (by omega) (writeIndex word i tapes)) := by
  let mid : (wordWriter word).Cfg :=
    ⟨.inr ⟨2 * i + 1, by dsimp [wordWriter]; omega⟩,
      Function.update tapes (1 : Fin 2) ((tapes 1).write word[i]?)⟩
  have h₁ : (wordWriter word).step (writerCfg word i hi.le tapes) = some mid := by
    simp [PrimitiveMachine.step, wordWriter, writerCfg, mid,
      show 2 * i < 2 * word.length by omega]
  have h₂ : (wordWriter word).step mid =
      some (writerCfg word (i + 1) (by omega) (writeIndex word i tapes)) := by
    have hlt : 2 * i + 1 < 2 * word.length := by omega
    have hmod : (2 * i + 1) % 2 ≠ 0 := by omega
    simp [PrimitiveMachine.step, wordWriter, writerCfg, mid, hlt,
      writeIndex, Nat.mul_add]
    funext k
    fin_cases k <;> rfl
  exact Trace.cons h₁ (Trace.cons h₂ (Trace.refl _))

/-- Iterated physical work-tape updates performed by the fixed writer. -/
def writeIndices (word : List Bool) (start count : ℕ)
    (tapes : Fin 2 → Tape (Option Bool)) : Fin 2 → Tape (Option Bool) :=
  match count with
  | 0 => tapes
  | count + 1 => writeIndices word (start + 1) count (writeIndex word start tapes)

theorem writer_segment (word : List Bool) (count start : ℕ)
    (h : start + count ≤ word.length) (tapes : Fin 2 → Tape (Option Bool)) :
    Trace (wordWriter word).step (2 * count)
      (writerCfg word start (by omega) tapes)
      (writerCfg word (start + count) h (writeIndices word start count tapes)) := by
  induction count generalizing start tapes with
  | zero => exact Trace.refl _
  | succ count ih =>
      have hi : start < word.length := by omega
      have hrest : start + 1 + count ≤ word.length := by omega
      have ht := (writer_pair word start hi tapes).trans
        (ih (start + 1) hrest (writeIndex word start tapes))
      simpa [writeIndices, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem writeIndex_preserves_input (word : List Bool) (i : ℕ)
    (tapes : Fin 2 → Tape (Option Bool)) : writeIndex word i tapes 0 = tapes 0 := by
  simp [writeIndex]

theorem writeIndices_preserves_input (word : List Bool) (start count : ℕ)
    (tapes : Fin 2 → Tape (Option Bool)) :
    writeIndices word start count tapes 0 = tapes 0 := by
  induction count generalizing start tapes with
  | zero => rfl
  | succ count ih =>
      rw [writeIndices, ih, writeIndex_preserves_input]

/-- Initialization by a fixed word has a proven input-independent primitive runtime. -/
theorem wordWriter_execution (word input : List Bool) :
    ∃ final : (wordWriter word).Cfg,
      RunsIn (wordWriter word).step (2 * word.length + 1)
        ((wordWriter word).init input) final ∧
      final.state = .inl false ∧
      final.tapes (0 : Fin 2) = ((wordWriter word).init input).tapes (0 : Fin 2) ∧
      final.tapes = writeIndices word 0 word.length ((wordWriter word).init input).tapes := by
  let tapes := ((wordWriter word).init input).tapes
  let out := writeIndices word 0 word.length tapes
  let final : (wordWriter word).Cfg := ⟨.inl false, out⟩
  have hseg := writer_segment word word.length 0 (by omega) tapes
  simp only [Nat.zero_add] at hseg
  have hend : (wordWriter word).step (writerCfg word word.length le_rfl out) = some final := by
    simp [PrimitiveMachine.step, writerCfg, wordWriter, final]
  have hall := hseg.trans (Trace.cons hend (Trace.refl final))
  refine ⟨final, ⟨2 * word.length + 1, le_rfl, ?_⟩, rfl, ?_, rfl⟩
  · simpa [writerCfg, tapes, PrimitiveMachine.init, wordWriter] using hall
  · exact writeIndices_preserves_input word 0 word.length tapes


open SubexponentialSAT.Computation Turing

/-- Direct physical writing of the listed bits, with the head advancing right. -/
def writeBits : List Bool → (Fin 2 → Tape (Option Bool)) → (Fin 2 → Tape (Option Bool))
  | [], tapes => tapes
  | bit :: rest, tapes =>
      writeBits rest (Function.update tapes 1 (((tapes 1).write (some bit)).move .right))

theorem writeIndices_cons_shift (bit : Bool) (word : List Bool) (count start : ℕ)
    (tapes : Fin 2 → Tape (Option Bool)) :
    writeIndices (bit :: word) (start + 1) count tapes =
      writeIndices word start count tapes := by
  induction count generalizing start tapes with
  | zero => rfl
  | succ count ih =>
      simp only [writeIndices]
      have hwrite : writeIndex (bit :: word) (start + 1) tapes = writeIndex word start tapes := by
        simp [writeIndex]
      rw [hwrite]
      exact ih (start + 1) (writeIndex word start tapes)

theorem writeIndices_full (word : List Bool) (tapes : Fin 2 → Tape (Option Bool)) :
    writeIndices word 0 word.length tapes = writeBits word tapes := by
  induction word generalizing tapes with
  | nil => rfl
  | cons bit word ih =>
      simp only [List.length_cons, writeIndices]
      rw [writeIndices_cons_shift bit word word.length 0]
      simpa [writeIndex, writeBits] using
        ih (Function.update tapes 1 (((tapes 1).write (some bit)).move .right))

theorem writeBits_tape (word : List Bool) (left : List (Option Bool))
    (tapes : Fin 2 → Tape (Option Bool))
    (h : tapes 1 = Tape.mk₂ left []) :
    writeBits word tapes 1 = Tape.mk₂ ((word.map some).reverse ++ left) [] := by
  induction word generalizing left tapes with
  | nil => simpa [writeBits] using h
  | cons bit word ih =>
      let next := Function.update tapes (1 : Fin 2) (((tapes 1).write (some bit)).move .right)
      have hn : next 1 = Tape.mk₂ (some bit :: left) [] := by
        simp only [next, Function.update_self, h]
        rfl
      have hi := ih (some bit :: left) next hn
      simpa [writeBits, next, List.reverse_cons, List.append_assoc] using hi

/-- The hardcoded word is physically present on the work tape after a constant
number of primitive steps, and the input tape is unchanged. -/
theorem wordWriter_correct (word input : List Bool) :
    ∃ final : (wordWriter word).Cfg,
      RunsIn (wordWriter word).step (2 * word.length + 1)
        ((wordWriter word).init input) final ∧
      final.state = .inl false ∧
      final.tapes (0 : Fin 2) = Tape.mk₁ (input.map some) ∧
      final.tapes (1 : Fin 2) = Tape.mk₂ (word.map some).reverse [] := by
  obtain ⟨final, hrun, hhalt, hin, hout⟩ := wordWriter_execution word input
  refine ⟨final, hrun, hhalt, ?_, ?_⟩
  · simpa [PrimitiveMachine.init, wordWriter] using hin
  · let initialTapes : Fin 2 → Tape (Option Bool) :=
      fun i => ((wordWriter word).init input).tapes i
    calc
      final.tapes (1 : Fin 2) =
          writeIndices word 0 word.length initialTapes 1 := by
        simpa only [initialTapes] using congrFun hout (1 : Fin 2)
      _ = writeBits word initialTapes 1 :=
        congrFun (writeIndices_full word initialTapes) 1
      _ = Tape.mk₂ (word.map some).reverse [] := by
        have hblank : initialTapes 1 = Tape.mk₂ [] [] := by
          simp [initialTapes, PrimitiveMachine.init, wordWriter, Tape.mk₁]
        simpa only [List.append_nil] using
          writeBits_tape word [] initialTapes hblank


open SubexponentialSAT.Computation Turing

/-- A finite deterministic scanner over the binary input alphabet. -/
structure Scanner where
  states : ℕ
  start : Fin states
  next : Fin states → Bool → Fin states
  accept : Fin states → Bool

def scannerMachine (s : Scanner) : PrimitiveMachine where
  tapeCount := 1
  stateCount := s.states
  inputTape := 0
  start := s.start
  scan _ := 0
  transition q symbol :=
    match symbol with
    | none => .inl (s.accept q)
    | some bit => .inr (s.next q bit, .move .right)

def scannerCfg (s : Scanner) (q : Fin s.states) (left : List (Option Bool))
    (remaining : List Bool) : (scannerMachine s).Cfg :=
  ⟨.inr q, fun _ => Tape.mk₂ left (remaining.map some)⟩

def scannerEval (s : Scanner) (q : Fin s.states) (word : List Bool) : Fin s.states :=
  word.foldl s.next q

def scannerFinal (s : Scanner) (q : Fin s.states) (left : List (Option Bool)) :
    (scannerMachine s).Cfg :=
  ⟨.inl (s.accept q), fun _ => Tape.mk₂ left []⟩

theorem scanner_step_bit (s : Scanner) (q : Fin s.states) (left : List (Option Bool))
    (bit : Bool) (remaining : List Bool) :
    (scannerMachine s).step (scannerCfg s q left (bit :: remaining)) =
      some (scannerCfg s (s.next q bit) (some bit :: left) remaining) := by
  simp only [PrimitiveMachine.step, scannerMachine, scannerCfg,
    List.map_cons, Tape.mk₂, Tape.mk', ListBlank.head_mk, List.headI_cons,
    ListBlank.tail_mk, List.tail_cons, Tape.move, ListBlank.cons_mk]
  congr 2
  funext k
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  change Tape.mk₂ (some bit :: left) (remaining.map some) =
    Tape.mk₂ (some bit :: left) (remaining.map some)
  rfl

theorem scanner_execution (s : Scanner) (word : List Bool) (q : Fin s.states)
    (left : List (Option Bool)) :
    Trace (scannerMachine s).step (word.length + 1)
      (scannerCfg s q left word)
      (scannerFinal s (scannerEval s q word) ((word.map some).reverse ++ left)) := by
  induction word generalizing q left with
  | nil => exact Trace.cons rfl (Trace.refl _)
  | cons bit word ih =>
      have hr := Trace.cons (scanner_step_bit s q left bit word)
        (ih (s.next q bit) (some bit :: left))
      simpa [scannerEval, List.reverse_cons, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hr

theorem scanner_outputs (s : Scanner) (input : List Bool) :
    (scannerMachine s).OutputsInTime input
      (s.accept (scannerEval s s.start input)) (input.length + 1) := by
  refine ⟨scannerFinal s (scannerEval s s.start input) (input.map some).reverse,
    ⟨input.length + 1, le_rfl, ?_⟩, rfl⟩
  have h := scanner_execution s input s.start []
  have hinit : (scannerMachine s).init input = scannerCfg s s.start [] input := by
    unfold PrimitiveMachine.init scannerCfg scannerMachine
    congr 1
    funext k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    simp [Tape.mk₁]
  simpa [hinit] using h


def suffixes (words : Finset (List Bool)) : Finset (List Bool) :=
  words.biUnion (fun word => word.tails.toFinset)

theorem word_mem_suffixes {words : Finset (List Bool)} {word : List Bool}
    (h : word ∈ words) : word ∈ suffixes words := by
  apply Finset.mem_biUnion.mpr
  refine ⟨word, h, ?_⟩
  exact List.mem_toFinset.mpr ((List.mem_tails word word).mpr ⟨[], rfl⟩)

theorem tail_mem_suffixes {words : Finset (List Bool)} {word : List Bool}
    (h : word ∈ suffixes words) : word.tail ∈ suffixes words := by
  obtain ⟨whole, hw, hword⟩ := Finset.mem_biUnion.mp h
  apply Finset.mem_biUnion.mpr
  refine ⟨whole, hw, ?_⟩
  apply List.mem_toFinset.mpr
  apply (List.mem_tails _ _).mpr
  have htail : word.tail <:+ word := by
    cases word with
    | nil => exact ⟨[], rfl⟩
    | cons bit rest => exact ⟨[bit], rfl⟩
  exact htail.trans ((List.mem_tails _ _).mp (List.mem_toFinset.mp hword))

def derivative (words : Finset (List Bool)) (bit : Bool) : Finset (List Bool) :=
  (words.filter (fun word => word.head? = some bit)).image List.tail

theorem mem_derivative (words : Finset (List Bool)) (bit : Bool) (rest : List Bool) :
    rest ∈ derivative words bit ↔ bit :: rest ∈ words := by
  constructor
  · intro h
    obtain ⟨word, hword, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hmem, hhead⟩ := Finset.mem_filter.mp hword
    cases word with
    | nil => simp at hhead
    | cons b tail =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        simp only [List.tail_cons] at heq
        subst b
        subst tail
        exact hmem
  · intro h
    apply Finset.mem_image.mpr
    exact ⟨bit :: rest, Finset.mem_filter.mpr ⟨h, rfl⟩, rfl⟩

theorem derivative_subset_suffixes (words R : Finset (List Bool))
    (hR : R ⊆ suffixes words) (bit : Bool) :
    derivative R bit ⊆ suffixes words := by
  intro rest hrest
  have hword := hR ((mem_derivative R bit rest).mp hrest)
  simpa using tail_mem_suffixes hword

def LanguageState (words : Finset (List Bool)) := ↥((suffixes words).powerset)

instance languageStateFintype (words : Finset (List Bool)) : Fintype (LanguageState words) := by
  unfold LanguageState
  infer_instance

def languageStart (words : Finset (List Bool)) : LanguageState words :=
  ⟨words, Finset.mem_powerset.mpr (fun _ h => word_mem_suffixes h)⟩

def languageNext (words : Finset (List Bool)) (state : LanguageState words) (bit : Bool) :
    LanguageState words :=
  ⟨derivative state.val bit,
    Finset.mem_powerset.mpr
      (derivative_subset_suffixes words state.val (Finset.mem_powerset.mp state.property) bit)⟩

theorem languageRun_mem (words : Finset (List Bool)) (input : List Bool)
    (state : LanguageState words) (suffix : List Bool) :
    suffix ∈ (input.foldl (languageNext words) state).val ↔ input ++ suffix ∈ state.val := by
  induction input generalizing state with
  | nil => rfl
  | cons bit input ih =>
      simp only [List.foldl_cons, List.cons_append]
      rw [ih]
      exact mem_derivative state.val bit (input ++ suffix)

noncomputable def scannerOfFinite {Q : Type} [Fintype Q]
    (start : Q) (next : Q → Bool → Q) (accept : Q → Bool) : Scanner where
  states := Fintype.card Q
  start := Fintype.equivFin Q start
  next q bit := Fintype.equivFin Q (next ((Fintype.equivFin Q).symm q) bit)
  accept q := accept ((Fintype.equivFin Q).symm q)

theorem scannerOfFinite_eval {Q : Type} [Fintype Q]
    (start : Q) (next : Q → Bool → Q) (accept : Q → Bool)
    (input : List Bool) (state : Q) :
    scannerEval (scannerOfFinite start next accept) (Fintype.equivFin Q state) input =
      Fintype.equivFin Q (input.foldl next state) := by
  induction input generalizing state with
  | nil => rfl
  | cons bit input ih =>
      simpa only [scannerEval, scannerOfFinite, List.foldl_cons,
        Equiv.symm_apply_apply] using ih (next state bit)

noncomputable def languageScanner (words : Finset (List Bool)) : Scanner :=
  scannerOfFinite (languageStart words) (languageNext words)
    (fun state => decide ([] ∈ state.val))

theorem languageScanner_accept (words : Finset (List Bool)) (input : List Bool) :
    (languageScanner words).accept
      (scannerEval (languageScanner words) (languageScanner words).start input) =
        decide (input ∈ words) := by
  unfold languageScanner
  rw [show (scannerOfFinite (languageStart words) (languageNext words)
      (fun state => decide ([] ∈ state.val))).start =
        Fintype.equivFin (LanguageState words) (languageStart words) from rfl]
  rw [scannerOfFinite_eval]
  simp only [scannerOfFinite, Equiv.symm_apply_apply]
  have h := languageRun_mem words input (languageStart words) []
  have h' : [] ∈ (input.foldl (languageNext words) (languageStart words)).val ↔
      input ∈ words := by
    simpa only [List.append_nil, languageStart] using h
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hd
    exact decide_eq_true (h'.mp (of_decide_eq_true hd))
  · intro hd
    exact decide_eq_true (h'.mpr (of_decide_eq_true hd))

theorem finiteLanguage_outputs (words : Finset (List Bool)) (input : List Bool) :
    (scannerMachine (languageScanner words)).OutputsInTime input
      (decide (input ∈ words)) (input.length + 1) := by
  rw [← languageScanner_accept words input]
  exact scanner_outputs _ _


def literalPairEquiv (n : ℕ) : (Fin n × Bool) ≃ SAT.Literal (Fin n) where
  toFun p := ⟨p.1, p.2⟩
  invFun l := (l.variable, l.positive)
  left_inv _ := rfl
  right_inv _ := rfl

instance smallLiteralFintype (n : ℕ) : Fintype (SAT.Literal (Fin n)) :=
  Fintype.ofEquiv (Fin n × Bool) (literalPairEquiv n)

def SmallFormula (B : ℕ) := (i : Fin (B + 1)) × SAT.CNF (Fin i.val)

instance smallFormulaFintype (B : ℕ) : Fintype (SmallFormula B) := by
  unfold SmallFormula
  infer_instance

def smallEncode {B : ℕ} (F : SmallFormula B) : List Bool := Encoding.encodeCNF F.2

/-- A finite, explicitly exhaustive precomputation for a fixed variable threshold. -/
def smallAcceptedWords (B : ℕ) : Finset (List Bool) :=
  (Finset.univ.filter (fun F : SmallFormula B => SAT.bruteForce F.2)).image smallEncode

theorem smallAcceptedWords_correct (B n : ℕ) (F : SAT.CNF (Fin n)) (hn : n ≤ B) :
    Encoding.encodeCNF F ∈ smallAcceptedWords B ↔ SAT.Satisfiable F := by
  constructor
  · intro h
    obtain ⟨G, hG, hcode⟩ := Finset.mem_image.mp h
    have hsat := (Finset.mem_filter.mp hG).2
    rcases G with ⟨⟨m, hm⟩, G⟩
    change Encoding.encodeCNF G = Encoding.encodeCNF F at hcode
    have hmn := Encoding.encodeCNF_numVariables G F hcode
    subst n
    have hGF := Encoding.encodeCNF_injective hcode
    subst F
    exact (SAT.bruteForce_eq_true_iff G).mp hsat
  · intro hsat
    apply Finset.mem_image.mpr
    refine ⟨⟨⟨n, by omega⟩, F⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (SAT.bruteForce_eq_true_iff F).mpr hsat⟩

/-- A real primitive machine for the bounded-variable branch. All truth-table
work is finite preprocessing, using the explicit exhaustive SAT evaluator. -/
noncomputable def smallSolver (B : ℕ) : PrimitiveMachine :=
  scannerMachine (languageScanner (smallAcceptedWords B))

theorem smallSolver_correct (B n : ℕ) (F : SAT.CNF (Fin n)) (hn : n ≤ B) :
    ∃ answer : Bool,
      (smallSolver B).OutputsInTime (Encoding.encodeCNF F) answer
        (Encoding.formulaBitLength F + 1) ∧
      (answer = true ↔ SAT.Satisfiable F) := by
  refine ⟨decide (Encoding.encodeCNF F ∈ smallAcceptedWords B), ?_, ?_⟩
  · exact finiteLanguage_outputs (smallAcceptedWords B) (Encoding.encodeCNF F)
  · simpa only [decide_eq_true_eq] using smallAcceptedWords_correct B n F hn

/-- The finite-threshold branch has a proved bit-machine runtime within the
candidate envelope. The machine depends on B, never on the varying formula. -/
theorem smallSolver_bound (B n : ℕ) (F : SAT.CNF (Fin n)) (hn : n ≤ B) :
    ∃ (answer : Bool) (time : ℕ),
      (smallSolver B).OutputsInTime (Encoding.encodeCNF F) answer time ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ runtimeBound 1 1 (9 / 10) (Encoding.formulaBitLength F) n := by
  obtain ⟨answer, hrun, hcorrect⟩ := smallSolver_correct B n F hn
  refine ⟨answer, Encoding.formulaBitLength F + 1, hrun, hcorrect, ?_⟩
  have he : (1 : ℝ) ≤ Real.rpow 2 ((9 / 10 : ℝ) * (n : ℝ)) := by
    apply Real.one_le_rpow (by norm_num)
    positivity
  simp only [runtimeBound, one_mul, pow_one, Nat.cast_add, Nat.cast_one]
  exact le_mul_of_one_le_right (by positivity) he

end SubexponentialSAT.FixedParameters

end OAI.Algorithms
