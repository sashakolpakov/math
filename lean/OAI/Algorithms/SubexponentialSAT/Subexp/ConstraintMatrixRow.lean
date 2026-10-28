import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintEntryProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixEmit

namespace OAI.Algorithms

/-! Fixed iteration over actual Side records. Each callback computes a
constraint entry, appends its scalar frame to the reversed row accumulator,
and restores the entry service's runtime context. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixRow

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes

abbrev Data := State 13 51

def entryRegisters : Fin 10 → Fin 13 := Fin.castAdd 3
def entryPorts : Fin 46 → Fin 51 := Fin.castAdd 5
def emitRegisters : Fin 3 → Fin 13 := Fin.castAdd 10
def emitPorts : Fin 3 → Fin 51 := ![0, 50, 49]

theorem entryRegisters_injective : Function.Injective entryRegisters := Fin.castAdd_injective _ _
theorem entryPorts_injective : Function.Injective entryPorts := Fin.castAdd_injective _ _
theorem emitRegisters_injective : Function.Injective emitRegisters := Fin.castAdd_injective _ _
theorem emitPorts_injective : Function.Injective emitPorts := by decide

theorem entryPorts_ne (j : Fin 46) (k : Fin 51) (hk : 46 ≤ k.val) : entryPorts j ≠ k := by
  intro h
  have hv : j.val = k.val := congrArg Fin.val h
  have hj := j.isLt
  omega

def recordPorts : RecordPrograms.Ports 13 51 :=
  ⟨10, 11, 12, 46, 47, by decide, by decide, by decide, by decide⟩

abbrev entry : Cmd 13 51 := .call
  (ProgramLinking.liftProgram ConstraintEntryProgram.program entryRegisters entryPorts)
abbrev emit : Cmd 13 51 := ConstraintMatrixEmit.call emitRegisters emitPorts
abbrev clear (src : Fin 51) : Cmd 13 51 := .call (clearProgram src 0 1)
abbrev callback : Cmd 13 51 := .seq (.call (transferProgram 47 24 0 1))
  (.seq entry (.seq emit (.seq (clear 0) (clear 24))))
abbrev command : Cmd 13 51 := RecordPrograms.iterate recordPorts callback
def program := compiled command 46 50

noncomputable def afterEntry (a : Data) (regs : Fin 10 → Bool) (answer : List Bool) : Data :=
  ⟨Function.extend entryRegisters regs a.regs, Function.update a.stacks 0 answer⟩

theorem afterEntry_register_frame (a : Data) (regs : Fin 10 → Bool) (answer : List Bool)
    (j : Fin 13) (hj : 10 ≤ j.val) : (afterEntry a regs answer).regs j = a.regs j := by
  apply Function.extend_apply'
  rintro ⟨k, hk⟩
  have hv := congrArg Fin.val hk
  have hlt := k.isLt
  simp only [entryRegisters, Fin.val_castAdd] at hv
  omega

variable {r Q Δ : ℕ}

def context (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u : UniversalType r Q Δ) (xs : List (ZMod p)) : Fin 46 → List Bool :=
  Function.update (ConstraintEntryProgram.input p i t u u xs (fun _ => false)).stacks 24 []

@[simp] theorem context_zero (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u : UniversalType r Q Δ) (xs : List (ZMod p)) : context p i t u xs 0 = [] := by
  rfl

@[simp] theorem context_right (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u : UniversalType r Q Δ) (xs : List (ZMod p)) : context p i t u xs 24 = [] := by
  simp [context]

theorem input_stacks (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) (regs : Fin 10 → Bool) :
    (ConstraintEntryProgram.input p i t u y xs regs).stacks =
      Function.update (context p i t u xs) 24 (CollisionProgram.encodeType y) := by
  funext j
  fin_cases j <;> rfl

theorem entry_eval (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) (xs : List (ZMod p))
    (a : Data)
    (ha : projectState entryRegisters entryPorts a =
      ConstraintEntryProgram.input p i t u y xs (a.regs ∘ entryRegisters)) :
    ∃ n ≤ ConstraintEntryProgram.programBudget p i t u y xs, ∃ out,
      Eval entry n a (afterEntry a out (word p (ConstraintEntryProgram.value p i t u y xs))) := by
  obtain ⟨out, n, hn, ht⟩ := ConstraintEntryProgram.program_runsIn p h2 i t u y xs
    (a.regs ∘ entryRegisters)
  have ht' : Trace ConstraintEntryProgram.program n
      ((projectState entryRegisters entryPorts a).withPC (some ConstraintEntryProgram.program.entry))
      ((ConstraintEntryProgram.output
        (ConstraintEntryProgram.input p i t u y xs (a.regs ∘ entryRegisters)) out
        (word p (ConstraintEntryProgram.value p i t u y xs))).withPC none) := by
    simpa only [ha] using ht
  have he := eval_call_from_state ConstraintEntryProgram.program entryRegisters entryPorts a
    entryRegisters_injective entryPorts_injective ht'
  have hb : Function.extend entryPorts (projectState entryRegisters entryPorts a).stacks a.stacks =
      a.stacks := congrArg StructuredProgram.State.stacks
        (embedState_project entryRegisters entryPorts a entryRegisters_injective entryPorts_injective)
  have hend : embedState entryRegisters entryPorts a
      (ConstraintEntryProgram.output
        (ConstraintEntryProgram.input p i t u y xs (a.regs ∘ entryRegisters)) out
        (word p (ConstraintEntryProgram.value p i t u y xs))) =
      afterEntry a out (word p (ConstraintEntryProgram.value p i t u y xs)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · change Function.extend entryPorts (Function.update _ 0 _) a.stacks = _
      rw [← ha, ProgramLinking.extend_update entryPorts_injective, hb]
      rfl
  exact ⟨n, hn, out, hend ▸ he⟩

def invariant (ctx : Fin 46 → List Bool) (a : Data) : Prop :=
  (∀ j, a.stacks (entryPorts j) = ctx j) ∧ a.stacks 48 = [] ∧ a.stacks 49 = []

def callbackCost (p E : ℕ) (bits : List Bool) : ℕ :=
  E + 5 * bits.length + 10 * width p + 17

def effect (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u : UniversalType r Q Δ) (xs : List (ZMod p)) (bits : List Bool) (a b : Data) : Prop :=
  ∀ y : UniversalType r Q Δ, CollisionProgram.encodeType y = bits →
    b.stacks 50 = (Encoding.frame (word p (ConstraintEntryProgram.value p i t u y xs))).reverse ++
      a.stacks 50

def validPayload (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u : UniversalType r Q Δ) (xs : List (ZMod p)) (E : ℕ) (bits : List Bool) : Prop :=
  ∃ y : UniversalType r Q Δ, bits = CollisionProgram.encodeType y ∧
    ConstraintEntryProgram.programBudget p i t u y xs ≤ E

theorem callback_contract (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (u : UniversalType r Q Δ) (xs : List (ZMod p)) (E : ℕ) :
    RecordPrograms.CallbackContractWithOn recordPorts callback (fun _ => false)
      (callbackCost p E) (invariant (context p i t u xs)) (effect p i t u xs)
      (validPayload p i t u xs E) := by
  intro bits tail base hv hi
  obtain ⟨y, rfl, hy⟩ := hv
  rcases hi with ⟨hctx, h48, h49⟩
  let bits := CollisionProgram.encodeType y
  let answer := word p (ConstraintEntryProgram.value p i t u y xs)
  let a := RecordPrograms.state recordPorts base false true false tail bits.reverse
  let b : Data := ⟨readRegs a.regs 0 1 none, transferStacks 47 24 a.stacks⟩
  have ha0 : a.stacks 0 = [] := by
    simpa [a, recordPorts, RecordPrograms.state, entryPorts,
      ConstraintEntryProgram.entryPorts]
      using hctx 0
  have ha24 : a.stacks 24 = [] := by
    simpa [a, recordPorts, RecordPrograms.state, entryPorts,
      ConstraintEntryProgram.entryPorts]
      using hctx 24
  have ha47 : a.stacks 47 = bits.reverse := by simp [a, recordPorts, RecordPrograms.state]
  have hb : projectState entryRegisters entryPorts b =
      ConstraintEntryProgram.input p i t u y xs (b.regs ∘ entryRegisters) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · change (projectState entryRegisters entryPorts b).stacks =
        (ConstraintEntryProgram.input p i t u y xs (b.regs ∘ entryRegisters)).stacks
      rw [input_stacks]
      funext j
      by_cases hj : j = 24
      · subst j
        simp [projectState, entryPorts, b, transferStacks, ha24, ha47, bits]
      · have hj24 : entryPorts j ≠ 24 := by
          intro h
          apply hj
          exact Fin.ext (congrArg (fun k : Fin 51 => k.val) h)
        have hj46 := entryPorts_ne j 46 (by decide)
        have hj47 := entryPorts_ne j 47 (by decide)
        simp [projectState, b, transferStacks, a, recordPorts, RecordPrograms.state,
          hj, hj24, hj46, hj47, hctx]
  have t0 := TupleProgram.transfer_eval (47 : Fin 51) 24 (0 : Fin 13) 1
    (by decide) (by decide) a
  obtain ⟨ne, hne, er, te⟩ := entry_eval p h2 i t u y xs b hb
  let c := afterEntry b er answer
  let d := ConstraintMatrixEmit.after emitRegisters emitPorts c
  let e : Data := ⟨readRegs d.regs 0 1 none, clearStacks 0 d.stacks⟩
  let f : Data := ⟨readRegs e.regs 0 1 none, clearStacks 24 e.stacks⟩
  have tc := ConstraintMatrixEmit.call_eval emitRegisters emitPorts
    emitRegisters_injective emitPorts_injective c
    (by simp [c, afterEntry, b, transferStacks, a, recordPorts, RecordPrograms.state, emitPorts, h49])
  have td := TupleProgram.clear_eval (0 : Fin 51) (0 : Fin 13) 1 d
  have tf := TupleProgram.clear_eval (24 : Fin 51) (0 : Fin 13) 1 e
  have hfstack : f.stacks = Function.update (Function.update a.stacks 47 []) 50
      ((Encoding.frame answer).reverse ++ a.stacks 50) := by
    funext j
    by_cases hj0 : j = 0
    · subst j; simp [f, e, clearStacks, ha0]
    by_cases hj24 : j = 24
    · subst j; simp [f, clearStacks, ha24]
    by_cases hj47 : j = 47
    · subst j; simp [f, e, clearStacks, d, ConstraintMatrixEmit.after, emitPorts,
        c, afterEntry, b, transferStacks]
    by_cases hj50 : j = 50
    · subst j; simp [f, e, clearStacks, d, ConstraintMatrixEmit.after, emitPorts,
        c, afterEntry, b, transferStacks]
    simp [f, e, clearStacks, d, ConstraintMatrixEmit.after, emitPorts,
      c, afterEntry, b, transferStacks, hj0, hj24, hj47, hj50]
  have hfreg (j : Fin 13) (hj : 10 ≤ j.val) : f.regs j = a.regs j := by
    have hj0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have hj1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    have hm : ¬ ∃ k, emitRegisters k = j := by
      rintro ⟨k, hk⟩
      have hv := congrArg Fin.val hk
      have hlt := k.isLt
      simp [emitRegisters] at hv
      omega
    simp only [f, e, readRegs, Function.update_of_ne hj1, Function.update_of_ne hj0]
    change d.regs j = a.regs j
    rw [ConstraintMatrixEmit.after_register_frame emitRegisters emitPorts c j hm]
    rw [afterEntry_register_frame b er answer j hj]
    simp [b, readRegs, hj0, hj1]
  have hfs : RecordPrograms.state recordPorts f false true false tail [] = f := by
    apply RecordPrograms.state_eq_self
    · simpa [recordPorts, a, RecordPrograms.state] using hfreg 10 (by decide)
    · simpa [recordPorts, a, RecordPrograms.state] using hfreg 11 (by decide)
    · simpa [recordPorts, a, RecordPrograms.state] using hfreg 12 (by decide)
    · simp [recordPorts, hfstack, a, RecordPrograms.state]
    · simp [recordPorts, hfstack]
  have hfi : invariant (context p i t u xs) f := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hj46 := entryPorts_ne j 46 (by decide)
      have hj47 := entryPorts_ne j 47 (by decide)
      have hj50 := entryPorts_ne j 50 (by decide)
      simp [hfstack, a, recordPorts, RecordPrograms.state, hj46, hj47, hj50, hctx]
    · simp [hfstack, a, recordPorts, RecordPrograms.state, h48]
    · simp [hfstack, a, recordPorts, RecordPrograms.state, h49]
  have hfe : effect p i t u xs bits base f := by
    intro z hz
    have hzy : z = y := CollisionProgram.encodeType_injective hz
    subst z
    simp [hfstack, a, recordPorts, RecordPrograms.state, answer]
  have hrun := t0.seq (te.seq (tc.seq (td.seq tf)))
  have hc0 : c.stacks (emitPorts 0) = answer := by simp [c, afterEntry, emitPorts]
  have hd0 : d.stacks 0 = answer := by
    simp [d, ConstraintMatrixEmit.after, emitPorts, c, afterEntry]
  have he24 : e.stacks 24 = bits := by
    simp [e, clearStacks, d, ConstraintMatrixEmit.after, emitPorts,
      c, afterEntry, b, transferStacks, ha24, ha47]
  refine ⟨3 * (a.stacks 47).length + 3 +
    (ne + (8 * (c.stacks (emitPorts 0)).length + 8 +
      (2 * (d.stacks 0).length + 3 + (2 * (e.stacks 24).length + 3)))),
    f, ?_, hfi, hfe, ?_⟩
  · rw [ha47, hc0, hd0, he24, List.length_reverse]
    simp only [answer, word_length, callbackCost]
    dsimp [bits]
    omega
  · rw [hfs]
    exact hrun

end SubexponentialSAT.Subexp.ConstraintMatrixRow

end OAI.Algorithms
