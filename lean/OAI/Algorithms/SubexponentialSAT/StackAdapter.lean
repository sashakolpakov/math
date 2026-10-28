import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.FixedParameters
import OAI.Algorithms.SubexponentialSAT.StackCompiler

namespace OAI.Algorithms

/-!
# Adapting the verified TM2 microstep expansion to finite stack programs

This layer handles finite source control, stack-index reindexing, raw input,
and the one-bit output convention. It supplies actual transition equations.
-/

namespace SubexponentialSAT.StackAdapter

open Turing SubexponentialSAT.Computation SubexponentialSAT.FixedParameters SubexponentialSAT.StackCompiler

abbrev SourceState (machine : BitMachine) := Control machine.tm × machine.tm.σ

instance stackFintype (machine : BitMachine) : Fintype machine.tm.K := machine.tm.kFin

def outputBit (machine : BitMachine) : Option (machine.tm.Γ machine.tm.k₁) → Bool
  | none => false
  | some value => machine.outputAlphabet value

def selectSource (machine : BitMachine) (q : SourceState machine) : machine.tm.K :=
  match q.1.val with
  | some (.push k _ _) => k
  | some (.peek k _ _) => k
  | some (.pop k _ _) => k
  | some .halt => machine.tm.k₁
  | none => machine.tm.k₁
  | _ => machine.tm.k₀

private def child (machine : BitMachine)
    {parent next : machine.tm.Stmt}
    (hp : some parent ∈ codeSet machine.tm) (hn : next ∈ TM2.stmts₁ parent) :
    Control machine.tm :=
  ⟨some next, TM2.stmts_trans hn hp⟩

private def target (machine : BitMachine) (l : machine.tm.Λ) (v : machine.tm.σ) :
    Control machine.tm :=
  ⟨some (machine.tm.m l), embed_code_mem machine.tm ⟨some l, v, fun _ => []⟩⟩

/-- Finite dispatch for one source micro-instruction. -/
def sourceTransition (machine : BitMachine) (q : SourceState machine) :
    Option (machine.tm.Γ (selectSource machine q)) →
      Bool ⊕ (SourceState machine × Mutation (machine.tm.Γ (selectSource machine q))) := by
  classical
  rcases q with ⟨⟨code, hcode⟩, v⟩
  cases code with
  | none => exact fun top => .inl (outputBit machine top)
  | some stmt =>
      cases stmt with
      | push k f next =>
          exact fun _ => .inr ((child machine (next := next) hcode (Finset.mem_insert_of_mem TM2.stmts₁_self), v),
            .push (f v))
      | peek k f next =>
          exact fun top => .inr ((child machine (next := next) hcode (Finset.mem_insert_of_mem TM2.stmts₁_self),
            f v top), .keep)
      | pop k f next =>
          exact fun top => .inr ((child machine (next := next) hcode (Finset.mem_insert_of_mem TM2.stmts₁_self),
            f v top), .pop)
      | load f next =>
          exact fun _ => .inr ((child machine (next := next) hcode (Finset.mem_insert_of_mem TM2.stmts₁_self),
            f v), .keep)
      | branch f yes no =>
          exact fun _ => if hf : f v then
            .inr ((child machine (next := yes) hcode (Finset.mem_insert_of_mem
              (Finset.mem_union_left _ TM2.stmts₁_self)), v), .keep)
          else
            .inr ((child machine (next := no) hcode (Finset.mem_insert_of_mem
              (Finset.mem_union_right _ TM2.stmts₁_self)), v), .keep)
      | goto f => exact fun _ => .inr ((target machine (f v) v, v), .keep)
      | halt => exact fun top => .inl (outputBit machine top)

structure SourceCfg (machine : BitMachine) where
  state : Bool ⊕ SourceState machine
  stk : ∀ k, List (machine.tm.Γ k)

def sourceStep (machine : BitMachine) (c : SourceCfg machine) : Option (SourceCfg machine) :=
  match c.state with
  | .inl _ => none
  | .inr q =>
      match sourceTransition machine q (c.stk (selectSource machine q)).head? with
      | .inl answer => some ⟨.inl answer, c.stk⟩
      | .inr (q', op) => some ⟨.inr q',
          Function.update c.stk (selectSource machine q) (op.apply (c.stk (selectSource machine q)))⟩

def sourceCfg (machine : BitMachine) (c : FiniteMicroCfg machine.tm) : SourceCfg machine :=
  ⟨match c.val.code with
    | none => .inl (outputBit machine (c.val.stk machine.tm.k₁).head?)
    | some _ => .inr (finiteControl machine.tm c),
    c.val.stk⟩

theorem sourceStep_of_microStep (machine : BitMachine)
    {a b : FiniteMicroCfg machine.tm} (h : finiteMicroStep machine.tm a = some b) :
    sourceStep machine (sourceCfg machine a) = some (sourceCfg machine b) := by
  have hs := congrArg (Option.map Subtype.val) h
  rw [finiteMicroStep_forget] at hs
  change microStep machine.tm a.val = some b.val at hs
  rcases a with ⟨⟨code, v, S⟩, ha⟩
  rcases b with ⟨b, hb⟩
  cases code with
  | none => simp [microStep] at hs
  | some stmt =>
      cases stmt with
      | push k f next =>
          simp only [microStep, Option.some.injEq] at hs
          subst b
          rfl
      | peek k f next =>
          simp only [microStep, Option.some.injEq] at hs
          subst b
          simp [sourceStep, sourceCfg, finiteControl, sourceTransition, selectSource,
            Mutation.apply, child, Function.update_eq_self]
      | pop k f next =>
          simp only [microStep, Option.some.injEq] at hs
          subst b
          rfl
      | load f next =>
          simp only [microStep, Option.some.injEq] at hs
          subst b
          simp [sourceStep, sourceCfg, finiteControl, sourceTransition, selectSource,
            Mutation.apply, child, Function.update_eq_self]
      | branch f yes no =>
          cases hf : f v <;>
            simp [microStep, hf] at hs <;>
            subst b <;>
            simp [sourceStep, sourceCfg, finiteControl, sourceTransition, selectSource,
              Mutation.apply, child, Function.update_eq_self, hf]
      | goto f =>
          simp only [microStep, Option.some.injEq] at hs
          subst b
          simp [sourceStep, sourceCfg, finiteControl, sourceTransition, selectSource,
            Mutation.apply, target, Function.update_eq_self]
      | halt =>
          simp only [microStep, Option.some.injEq] at hs
          subst b
          rfl

theorem sourceTrace_of_microTrace (machine : BitMachine)
    {a b : FiniteMicroCfg machine.tm} {steps : ℕ}
    (h : Trace (finiteMicroStep machine.tm) steps a b) :
    Trace (sourceStep machine) steps (sourceCfg machine a) (sourceCfg machine b) := by
  induction h with
  | refl => exact Trace.refl _
  | cons hs ht ih => exact Trace.cons (sourceStep_of_microStep machine hs) ih

noncomputable def stackEquiv (machine : BitMachine) :
    machine.tm.K ≃ Fin (Fintype.card machine.tm.K) := Fintype.equivFin _

def Alphabet (machine : BitMachine) (i : Fin (Fintype.card machine.tm.K)) : Type :=
  machine.tm.Γ ((stackEquiv machine).symm i)

noncomputable def symbolEquiv (machine : BitMachine) (k : machine.tm.K) :
    machine.tm.Γ k ≃ Alphabet machine (stackEquiv machine k) :=
  Equiv.cast (congrArg machine.tm.Γ ((stackEquiv machine).symm_apply_apply k).symm)

def mapMutation {α β : Type} (f : α → β) : Mutation α → Mutation β
  | .keep => .keep
  | .pop => .pop
  | .push a => .push (f a)

theorem mapMutation_apply {α β : Type} (f : α → β) (op : Mutation α) (s : List α) :
    (mapMutation f op).apply (s.map f) = (op.apply s).map f := by
  cases op <;> simp [mapMutation, Mutation.apply]

noncomputable def indexStacks (machine : BitMachine) (S : ∀ k, List (machine.tm.Γ k)) :
    ∀ i, List (Alphabet machine i) :=
  fun i => S ((stackEquiv machine).symm i)

private theorem dependent_list_cast {ι : Type} (Γ : ι → Type) (S : ∀ i, List (Γ i))
    {i j : ι} (h : i = j) :
    S i = (S j).map (Equiv.cast (congrArg Γ h.symm)) := by
  cases h
  simp

theorem indexStacks_at (machine : BitMachine) (S : ∀ k, List (machine.tm.Γ k))
    (k : machine.tm.K) :
    indexStacks machine S (stackEquiv machine k) = (S k).map (symbolEquiv machine k) := by
  exact dependent_list_cast machine.tm.Γ S ((stackEquiv machine).symm_apply_apply k)

theorem indexStacks_head (machine : BitMachine) (S : ∀ k, List (machine.tm.Γ k))
    (k : machine.tm.K) :
    ((indexStacks machine S (stackEquiv machine k)).head?).map
      (symbolEquiv machine k).symm = (S k).head? := by
  rw [indexStacks_at]
  simp

theorem indexStacks_update (machine : BitMachine) (S : ∀ k, List (machine.tm.Γ k))
    (k : machine.tm.K) (op : Mutation (machine.tm.Γ k)) :
    indexStacks machine (Function.update S k (op.apply (S k))) =
      Function.update (indexStacks machine S) (stackEquiv machine k)
        ((mapMutation (symbolEquiv machine k) op).apply
          (indexStacks machine S (stackEquiv machine k))) := by
  funext i
  by_cases hi : i = stackEquiv machine k
  · subst i
    rw [Function.update_self, indexStacks_at, indexStacks_at,
      Function.update_self, mapMutation_apply]
  · have hk : (stackEquiv machine).symm i ≠ k := by
      intro h
      apply hi
      rw [← h, Equiv.apply_symm_apply]
    simp [indexStacks, Function.update_of_ne hi, Function.update_of_ne hk]
    rfl

noncomputable def program (machine : BitMachine) :
    StackProgram (SourceState machine) (Alphabet machine) where
  inputTape := stackEquiv machine machine.tm.k₀
  start := (target machine machine.tm.main machine.tm.initialState, machine.tm.initialState)
  select q := stackEquiv machine (selectSource machine q)
  transition q top :=
    match sourceTransition machine q (top.map (symbolEquiv machine (selectSource machine q)).symm) with
    | .inl answer => .inl answer
    | .inr (q', op) => .inr (q', mapMutation (symbolEquiv machine (selectSource machine q)) op)

noncomputable def indexedCfg (machine : BitMachine) (c : SourceCfg machine) :
    StackCfg (SourceState machine) (Alphabet machine) :=
  ⟨c.state, indexStacks machine c.stk⟩

theorem indexed_step (machine : BitMachine) (c : SourceCfg machine) :
    stackStep (program machine) (indexedCfg machine c) =
      (sourceStep machine c).map (indexedCfg machine) := by
  rcases c with ⟨state, S⟩
  cases state with
  | inl answer => rfl
  | inr q =>
      simp only [stackStep, program, indexedCfg, sourceStep, indexStacks_head]
      cases h : sourceTransition machine q (S (selectSource machine q)).head? with
      | inl answer => rfl
      | inr out =>
          rcases out with ⟨q', op⟩
          exact congrArg (fun S => some (⟨.inr q', S⟩ :
            StackCfg (SourceState machine) (Alphabet machine)))
            (indexStacks_update machine S (selectSource machine q) op).symm

noncomputable def adaptedCfg (machine : BitMachine) (c : FiniteMicroCfg machine.tm) :
    StackCfg (SourceState machine) (Alphabet machine) :=
  indexedCfg machine (sourceCfg machine c)

theorem adapted_step (machine : BitMachine) {a b : FiniteMicroCfg machine.tm}
    (h : finiteMicroStep machine.tm a = some b) :
    stackStep (program machine) (adaptedCfg machine a) = some (adaptedCfg machine b) := by
  rw [adaptedCfg, indexed_step, sourceStep_of_microStep machine h]
  rfl

theorem adapted_trace (machine : BitMachine) {a b : FiniteMicroCfg machine.tm} {steps : ℕ}
    (h : Trace (finiteMicroStep machine.tm) steps a b) :
    Trace (stackStep (program machine)) steps (adaptedCfg machine a) (adaptedCfg machine b) := by
  induction h with
  | refl => exact Trace.refl _
  | cons hs ht ih => exact Trace.cons (adapted_step machine hs) ih

noncomputable instance alphabetFintype (machine : BitMachine)
    (i : Fin (Fintype.card machine.tm.K)) : Fintype (Alphabet machine i) := by
  letI : Finite (Alphabet machine i) := machine.finiteAlphabet _
  exact Fintype.ofFinite _

noncomputable def inputAlphabet (machine : BitMachine) :
    Alphabet machine (program machine).inputTape ≃ Bool :=
  (symbolEquiv machine machine.tm.k₀).symm.trans machine.inputAlphabet

def readBoolCode {α : Type} (e : α ≃ Bool) : List Bool → Option α
  | [bit] => some (e.symm bit)
  | _ => none

noncomputable def codes (machine : BitMachine) : CodeFamily (Alphabet machine) := by
  classical
  intro i
  by_cases hi : i = (program machine).inputTape
  · subst i
    exact StackEncoding.codeOfBoolEquiv (inputAlphabet machine)
  · exact StackEncoding.codeOfEquiv (Fintype.equivFin (Alphabet machine i))

noncomputable def decoder (machine : BitMachine)
    (i : Fin (Fintype.card machine.tm.K)) : List Bool → Option (Alphabet machine i) := by
  classical
  by_cases hi : i = (program machine).inputTape
  · subst i
    exact readBoolCode (inputAlphabet machine)
  · exact StackEncoding.readCodeOfEquiv (Fintype.equivFin (Alphabet machine i))

theorem codes_input (machine : BitMachine) :
    codes machine (program machine).inputTape =
      StackEncoding.codeOfBoolEquiv (inputAlphabet machine) := by
  simp [codes]

theorem decoder_nil (machine : BitMachine) (i : Fin (Fintype.card machine.tm.K)) :
    decoder machine i [] = none := by
  classical
  by_cases hi : i = (program machine).inputTape
  · subst i
    simp [decoder, readBoolCode]
  · simp [decoder, hi]

theorem decoder_block (machine : BitMachine) (i : Fin (Fintype.card machine.tm.K))
    (a : Alphabet machine i) : decoder machine i ((codes machine i).block a) = some a := by
  classical
  by_cases hi : i = (program machine).inputTape
  · subst i
    simp [decoder, codes, StackEncoding.codeOfBoolEquiv, readBoolCode]
  · simp [decoder, codes, hi]

theorem indexStacks_set (machine : BitMachine) (S : ∀ k, List (machine.tm.Γ k))
    (k : machine.tm.K) (s : List (machine.tm.Γ k)) :
    indexStacks machine (Function.update S k s) =
      Function.update (indexStacks machine S) (stackEquiv machine k)
        (s.map (symbolEquiv machine k)) := by
  funext i
  by_cases hi : i = stackEquiv machine k
  · subst i
    rw [Function.update_self, indexStacks_at, Function.update_self]
  · have hk : (stackEquiv machine).symm i ≠ k := by
      intro h
      apply hi
      rw [← h, Equiv.apply_symm_apply]
    simp [indexStacks, Function.update_of_ne hi, Function.update_of_ne hk]
    rfl

theorem adapted_initial (machine : BitMachine) (input : List Bool) :
    adaptedCfg machine (finiteEmbed machine.tm
      (Turing.initList machine.tm (input.map machine.inputAlphabet.symm))) =
        initialCfg (program machine) (inputAlphabet machine) input := by
  have hstk : (Turing.initList machine.tm (input.map machine.inputAlphabet.symm)).stk =
      Function.update (fun _ => []) machine.tm.k₀ (input.map machine.inputAlphabet.symm) := by
    funext k
    by_cases hk : k = machine.tm.k₀
    · subst k
      simp [Turing.initList]
    · simp [Turing.initList, hk]
  change (⟨.inr (program machine).start,
      indexStacks machine (Turing.initList machine.tm (input.map machine.inputAlphabet.symm)).stk⟩ :
      StackCfg (SourceState machine) (Alphabet machine)) = _
  rw [hstk, indexStacks_set]
  simp only [initialCfg, inputAlphabet,
    List.map_map]
  rfl

theorem adapted_terminal (machine : BitMachine) (answer : Bool) :
    (adaptedCfg machine (finiteEmbed machine.tm
      (Turing.haltList machine.tm ([answer].map machine.outputAlphabet.symm)))).state =
        .inl answer := by
  simp [adaptedCfg, indexedCfg, sourceCfg, finiteEmbed, embed, Turing.haltList, outputBit]

theorem macro_stack_execution (machine : BitMachine) {a b : machine.tm.Cfg} {time : ℕ}
    (h : RunsIn machine.tm.step time a b) :
    RunsIn (stackStep (program machine)) (blockOverhead machine.tm * time)
      (adaptedCfg machine (finiteEmbed machine.tm a))
      (adaptedCfg machine (finiteEmbed machine.tm b)) := by
  obtain ⟨steps, hsteps, htrace⟩ := finite_micro_execution machine.tm h
  exact ⟨steps, hsteps, adapted_trace machine htrace⟩

/-- The fully specified primitive-bit compilation of the fixed source machine. -/
noncomputable def compiledMachine (machine : BitMachine) : PrimitiveMachine :=
  StackCompiler.compiledMachine (program machine) (codes machine) (decoder machine)

noncomputable def compiledSourceCfg (machine : BitMachine) (c : machine.tm.Cfg) :
    (compiledMachine machine).Cfg :=
  StackCompiler.compiledCfg (program machine) (codes machine) (decoder machine)
    (adaptedCfg machine (finiteEmbed machine.tm c))

/-- Fixed source-block size times fixed alphabet/block-code simulation cost. -/
noncomputable def overhead (machine : BitMachine) : ℕ :=
  compilerOverhead (codes machine) * blockOverhead machine.tm

theorem overhead_pos (machine : BitMachine) : 0 < overhead machine :=
  Nat.mul_pos (compilerOverhead_pos (program machine) (codes machine))
    (blockOverhead_pos machine.tm)

/-- Actual source traces become actual primitive traces at fixed multiplicative cost. -/
theorem compiled_execution (machine : BitMachine) {a b : machine.tm.Cfg} {time : ℕ}
    (h : RunsIn machine.tm.step time a b) :
    RunsIn (compiledMachine machine).step (overhead machine * time)
      (compiledSourceCfg machine a) (compiledSourceCfg machine b) := by
  have hstack := macro_stack_execution machine h
  obtain ⟨c, hc, hrun⟩ := simulate_runsIn
    (primitive_simulation (program machine) (codes machine) (decoder machine)
      (decoder_nil machine) (decoder_block machine)) hstack rfl
  simpa only [hc, compiledMachine, compiledSourceCfg, overhead, Nat.mul_assoc] using hrun

theorem compiled_initial (machine : BitMachine) (input : List Bool) :
    compiledSourceCfg machine
      (Turing.initList machine.tm (input.map machine.inputAlphabet.symm)) =
        (compiledMachine machine).init input := by
  unfold compiledSourceCfg compiledMachine
  rw [adapted_initial]
  exact StackCompiler.compiled_initial (program machine) (codes machine) (decoder machine)
    (inputAlphabet machine) (codes_input machine) input

theorem compiled_terminal (machine : BitMachine) (answer : Bool) :
    (compiledSourceCfg machine
      (Turing.haltList machine.tm ([answer].map machine.outputAlphabet.symm))).state =
        .inl answer :=
  StackCompiler.compiled_terminal (program machine) (codes machine) (decoder machine)
    _ answer (adapted_terminal machine answer)

/-- A proved concrete compiler certificate, with every decoder and trace obligation discharged. -/
noncomputable def simulation (machine : BitMachine) :
    MacroToPrimitiveSimulation machine (compiledMachine machine) (overhead machine) where
  related source target := target = compiledSourceCfg machine source
  initial input := (compiled_initial machine input).symm
  transition := by
    intro a a' b hb hstep
    subst b
    refine ⟨compiledSourceCfg machine a', rfl, ?_⟩
    have hrun : RunsIn machine.tm.step 1 a a' :=
      ⟨1, le_rfl, Trace.cons hstep (Trace.refl a')⟩
    simpa using compiled_execution machine hrun
  terminal := by
    intro answer c hc
    subst c
    exact compiled_terminal machine answer

/-- A fixed-alphabet TM2 bound is sufficient: this theorem supplies the actual
constant-overhead primitive compiler rather than assuming one exists. -/
theorem macrostep_to_primitive {width : ℕ} {exponent : ℝ}
    (h : MacrostepExponentFeasible width exponent) : ExponentFeasible width exponent := by
  obtain ⟨machine, constant, degree, hc, hd, hbound⟩ := h
  exact exponentFeasible_of_macro_simulation (simulation machine)
    (overhead_pos machine) hc hd hbound

end SubexponentialSAT.StackAdapter

end OAI.Algorithms
