import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CoreMaskProgram
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Core selection from the first gathered clause

The gathered-family order is retained: the first record is the clause to which
the forward mask applies. The family is preserved. The mask is consumed by
exactly the number of literals in that first clause, and all work stacks are
empty at return. An empty family produces the encoded empty core.
-/

namespace SubexponentialSAT.FirstClauseCoreProgram

open BitProgram StructuredCalls

abbrev Clause := List (List Bool)
abbrev Family := List Clause
abbrev Data := State 4 6

def clauseCode (C : Clause) : List Bool := Encoding.encodeList id C
def familyCode (G : Family) : List Bool := Encoding.encodeList clauseCode G

def slots (family mask output scan clause temp : List Bool) : Fin 6 → List Bool :=
  fun i => if i = 0 then family else if i = 1 then mask else if i = 2 then output
    else if i = 3 then scan else if i = 4 then clause else temp

@[simp] theorem slots_zero (a b c d e f : List Bool) : slots a b c d e f 0 = a := rfl
@[simp] theorem slots_one (a b c d e f : List Bool) : slots a b c d e f 1 = b := rfl
@[simp] theorem slots_two (a b c d e f : List Bool) : slots a b c d e f 2 = c := rfl
@[simp] theorem slots_three (a b c d e f : List Bool) : slots a b c d e f 3 = d := rfl
@[simp] theorem slots_four (a b c d e f : List Bool) : slots a b c d e f 4 = e := rfl
@[simp] theorem slots_five (a b c d e f : List Bool) : slots a b c d e f 5 = f := rfl

@[simp] theorem update_slots_three (a b c d e f x : List Bool) :
    Function.update (slots a b c d e f) 3 x = slots a b c x e f := by
  funext i; fin_cases i <;> simp [slots]

@[simp] theorem update_slots_four (a b c d e f x : List Bool) :
    Function.update (slots a b c d e f) 4 x = slots a b c d x f := by
  funext i; fin_cases i <;> simp [slots]

def state (regs : Fin 4 → Bool) (family mask output scan clause temp : List Bool) : Data :=
  ⟨regs, slots family mask output scan clause temp⟩

abbrev copyFamily : Cmd 4 6 := .call (StackRoutines.copyProgram 0 3 5 0 1)
abbrev clearScan : Cmd 4 6 := .call (StackRoutines.clearProgram 3 0 1)
abbrev reverseClause : Cmd 4 6 := .call (StackRoutines.reverseProgram 4 3 5 0 1)

theorem copyFamily_eval (regs : Fin 4 → Bool) (family mask : List Bool) :
    Eval copyFamily (7 * family.length + 5)
      (state regs family mask [] [] [] [])
      (state (readRegs regs 0 1 none) family mask [] family [] []) := by
  have h := StackRoutines.copyProgram_trace (0 : Fin 6) 3 5 (0 : Fin 4) 1
    (by decide) (by decide) (by decide) (by decide) regs (slots family mask [] [] [] []) rfl
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  apply Eval.call
  simpa [StackRoutines.copyProgram, StackRoutines.copyResult, StackRoutines.copyStacks,
    state, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem clearScan_eval (regs : Fin 4 → Bool) (family mask scan clause : List Bool) :
    Eval clearScan (2 * scan.length + 3)
      (state regs family mask [] scan clause [])
      (state (readRegs regs 0 1 none) family mask [] [] clause []) := by
  have h := StackRoutines.clearProgram_trace (3 : Fin 6) (0 : Fin 4) 1
    regs (slots family mask [] scan clause [])
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  apply Eval.call
  simpa [StackRoutines.clearProgram, StackRoutines.clearResult, StackRoutines.clearStacks,
    state, StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem reverseClause_eval (regs : Fin 4 → Bool) (family mask clause : List Bool) :
    Eval reverseClause (9 * clause.length + 7)
      (state regs family mask [] [] clause [])
      (state (readRegs regs 0 1 none) family mask [] [] clause.reverse []) := by
  have h := StackRoutines.reverseProgram_trace (4 : Fin 6) 3 5 (0 : Fin 4) 1
    (by decide) (by decide) (by decide) (by decide)
    regs (slots family mask [] [] clause []) rfl rfl
  have hh := StackRoutines.halt_after_trace _ h 9 rfl rfl
  apply Eval.call
  simpa [StackRoutines.reverseProgram, StackRoutines.reverseResult, StackRoutines.reverseStacks,
    state, StructuredProgram.State.withPC, Nat.add_assoc] using hh

def ports : RecordPrograms.Ports 4 6 where
  tag := 0
  present := 1
  found := 2
  source := 3
  payload := 4
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev readClause : Cmd 4 6 := RecordPrograms.reader ports

theorem readClause_eval (regs : Fin 4 → Bool) (family mask bits rest : List Bool) :
    Eval readClause (6 * bits.length + 4)
      (state regs family mask [] (Encoding.frame bits ++ rest) [] [])
      (state (readRegs regs 0 1 (some false)) family mask [] rest bits.reverse []) := by
  let d := state regs family mask [] (Encoding.frame bits ++ rest) [] []
  have h := RecordPrograms.reader_eval ports d bits rest [] (regs 0) (regs 1) (regs 2)
  have hi : RecordPrograms.state ports d (regs 0) (regs 1) (regs 2)
      (Encoding.frame bits ++ rest) [] = d := by
    apply RecordPrograms.state_eq_self <;> rfl
  have ho : RecordPrograms.state ports d false true (regs 2) rest bits.reverse =
      state (readRegs regs 0 1 (some false)) family mask [] rest bits.reverse [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ ports, d, state, readRegs]
    · simp [ ports, d, state]
  simpa only [hi, List.append_nil, ho, readClause] using h

abbrev popFirst : Cmd 4 6 := RecordPrograms.atom (.pop 3 0 1)

theorem popFirst_eval (regs : Fin 4 → Bool) (family mask tail : List Bool) (bit : Bool) :
    Eval popFirst 1 (state regs family mask [] (bit :: tail) [] [])
      (state (readRegs regs 0 1 (some bit)) family mask [] tail [] []) := by
  have h : (StructuredProgram.Atom.pop (r := 4) (s := 6) 3 0 1).eval
      (state regs family mask [] (bit :: tail) [] []) =
      state (readRegs regs 0 1 (some bit)) family mask [] tail [] [] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, state]
  rw [← h]
  exact .base (.atom _ _)

abbrev emptyClause : Cmd 4 6 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push 4 0))

theorem emptyClause_eval (regs : Fin 4 → Bool) (family mask : List Bool) :
    Eval emptyClause 2 (state regs family mask [] [] [] [])
      (state (Function.update regs 0 false) family mask [] [] [false] []) := by
  have h1 : (StructuredProgram.Atom.set (r := 4) (s := 6) 0 false).eval
      (state regs family mask [] [] [] []) =
      state (Function.update regs 0 false) family mask [] [] [] [] := rfl
  have h2 : (StructuredProgram.Atom.push (r := 4) (s := 6) 4 0).eval
      (state (Function.update regs 0 false) family mask [] [] [] []) =
      state (Function.update regs 0 false) family mask [] [] [false] [] := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, state]
  have a : Eval (RecordPrograms.atom (.set 0 false)) 1
      (state regs family mask [] [] [] [])
      (state (Function.update regs 0 false) family mask [] [] [] []) := by
    rw [← h1]; exact .base (.atom _ _)
  have b : Eval (RecordPrograms.atom (.push 4 0)) 1
      (state (Function.update regs 0 false) family mask [] [] [] [])
      (state (Function.update regs 0 false) family mask [] [] [false] []) := by
    rw [← h2]; exact .base (.atom _ _)
  exact Eval.seq a b

abbrev nonemptyClause : Cmd 4 6 := .seq readClause (.seq clearScan reverseClause)
abbrev prepare : Cmd 4 6 := .seq copyFamily (.seq popFirst (.ite 0 nonemptyClause emptyClause))

theorem prepare_eval (G : Family) (mask : List Bool) (regs : Fin 4 → Bool) :
    ∃ n ≤ 30 * (familyCode G).length + 30, ∃ regs' : Fin 4 → Bool,
      Eval prepare n (state regs (familyCode G) mask [] [] [] [])
        (state regs' (familyCode G) mask [] [] (clauseCode (G.headD [])) []) := by
  let r := readRegs regs 0 1 none
  have hc := copyFamily_eval regs (familyCode G) mask
  cases G with
  | nil =>
    let r' := readRegs r 0 1 (some false)
    have hp := popFirst_eval r (familyCode []) mask [] false
    have he := emptyClause_eval r' (familyCode []) mask
    have hi : Eval (.ite 0 nonemptyClause emptyClause) 3
        (state r' (familyCode []) mask [] [] [] [])
        (state (Function.update r' 0 false) (familyCode []) mask [] [] [false] []) :=
      Eval.ite_false (by simp [state, r', readRegs]) he
    refine ⟨(7 * (familyCode []).length + 5) + (1 + 3), ?_, Function.update r' 0 false, ?_⟩
    · simp [familyCode, Encoding.encodeList]
    · simpa [prepare, familyCode, clauseCode, Encoding.encodeList] using Eval.seq hc (Eval.seq hp hi)
  | cons C rest =>
    let r' := readRegs r 0 1 (some true)
    let rp := readRegs r' 0 1 (some false)
    let rc := readRegs rp 0 1 none
    let rr := readRegs rc 0 1 none
    have hp := popFirst_eval r (familyCode (C :: rest)) mask
      (Encoding.frame (clauseCode C) ++ familyCode rest) true
    have hr := readClause_eval r' (familyCode (C :: rest)) mask (clauseCode C) (familyCode rest)
    have hx := clearScan_eval rp (familyCode (C :: rest)) mask (familyCode rest) (clauseCode C).reverse
    have hv := reverseClause_eval rc (familyCode (C :: rest)) mask (clauseCode C).reverse
    simp only [List.length_reverse, List.reverse_reverse] at hv
    have hn : Eval nonemptyClause
        ((6 * (clauseCode C).length + 4) +
          ((2 * (familyCode rest).length + 3) + (9 * (clauseCode C).length + 7)))
        (state r' (familyCode (C :: rest)) mask []
          (Encoding.frame (clauseCode C) ++ familyCode rest) [] [])
        (state rr (familyCode (C :: rest)) mask [] [] (clauseCode C) []) :=
      Eval.seq hr (Eval.seq hx hv)
    have hi := Eval.ite_true (test := (0 : Fin 4))
      (by simp [state, r', readRegs]) hn (no := emptyClause)
    refine ⟨(7 * (familyCode (C :: rest)).length + 5) +
      (1 + (((6 * (clauseCode C).length + 4) +
        ((2 * (familyCode rest).length + 3) + (9 * (clauseCode C).length + 7))) + 1)),
      ?_, rr, ?_⟩
    · simp only [familyCode, Encoding.length_encodeList_cons]
      omega
    · simpa [prepare, familyCode, Encoding.encodeList] using Eval.seq hc (Eval.seq hp hi)

def maskStack (i : Fin 4) : Fin 6 :=
  if i = 0 then 4 else if i = 1 then 1 else if i = 2 then 5 else 2

theorem maskStack_injective : Function.Injective maskStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [maskStack]

abbrev selectCore : Cmd 4 6 :=
  .call (ProgramLinking.liftProgram CoreMaskProgram.program id maskStack)

theorem selectCore_eval (C : Clause) (family mask : List Bool) (regs : Fin 4 → Bool) :
    ∃ n ≤ CoreMaskProgram.runtimeBound C,
      Eval selectCore n (state regs family mask [] [] (clauseCode C) [])
        (state (fun _ => false) family (mask.drop C.length)
          (clauseCode (CoreMaskProgram.select mask C)) [] [] []) := by
  obtain ⟨n, hn, htrace⟩ := CoreMaskProgram.run_correct C [] mask (regs 0) (regs 1) (regs 2) (regs 3)
  simp only [List.append_nil] at htrace
  let a := CoreMaskProgram.state (regs 0) (regs 1) (regs 2) (regs 3)
    (clauseCode C) mask [] []
  let b := CoreMaskProgram.state false false false false [] (mask.drop C.length) []
    (clauseCode (CoreMaskProgram.select mask C))
  let frame := state regs family mask [] [] (clauseCode C) []
  have ha : embedState id maskStack frame a = frame := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id maskStack_injective
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      rfl
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      rfl
  have hb : embedState id maskStack frame b =
      state (fun _ => false) family (mask.drop C.length)
        (clauseCode (CoreMaskProgram.select mask C)) [] [] [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id maskStack_injective
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      exact False.elim (hi ⟨i, rfl⟩)
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · rfl
      · exact False.elim (hi ⟨1, rfl⟩)
      · exact False.elim (hi ⟨3, rfl⟩)
      · rfl
      · exact False.elim (hi ⟨0, rfl⟩)
      · exact False.elim (hi ⟨2, rfl⟩)
  have h := eval_call_lifted CoreMaskProgram.program id maskStack frame
    Function.injective_id maskStack_injective (a := a) (b := b) htrace
  refine ⟨n, hn, ?_⟩
  simpa only [ha, hb, selectCore] using h

abbrev command : Cmd 4 6 := .seq prepare selectCore
def program := compiled command 0 2

def bound (G : Family) : ℕ := 50 * (familyCode G).length + 50

theorem firstClause_length_le (G : Family) :
    (clauseCode (G.headD [])).length ≤ (familyCode G).length := by
  cases G with
  | nil => simp [clauseCode, familyCode, Encoding.encodeList]
  | cons C G =>
    simp only [List.headD_cons, familyCode, Encoding.length_encodeList_cons]
    omega

theorem command_eval (G : Family) (mask : List Bool) (regs : Fin 4 → Bool) :
    ∃ n, n + 1 ≤ bound G ∧
      Eval command n (state regs (familyCode G) mask [] [] [] [])
        (state (fun _ => false) (familyCode G) (mask.drop (G.headD []).length)
          (clauseCode (CoreMaskProgram.select mask (G.headD []))) [] [] []) := by
  obtain ⟨n, hn, regs', hp⟩ := prepare_eval G mask regs
  obtain ⟨m, hm, hs⟩ := selectCore_eval (G.headD []) (familyCode G) mask regs'
  refine ⟨n + m, ?_, Eval.seq hp hs⟩
  have hlen := firstClause_length_le G
  dsimp [CoreMaskProgram.runtimeBound] at hm
  dsimp [clauseCode] at hlen
  dsimp [bound]
  omega

/-- The exact mask suffix is retained. Missing mask bits mean false and excess
bits remain unread, as specified by the checked selector. -/
theorem program_runsIn (G : Family) (mask : List Bool) (regs : Fin 4 → Bool) :
    RunsIn program (bound G)
      ((state regs (familyCode G) mask [] [] [] []).withPC (some program.entry))
      ((state (fun _ => false) (familyCode G) (mask.drop (G.headD []).length)
        (clauseCode (CoreMaskProgram.select mask (G.headD []))) [] [] []).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_eval G mask regs
  exact ⟨n + 1, hn, compiled_halt_trace he 0 2⟩

theorem state_eq (d : Data) (G : Family) (mask : List Bool)
    (h0 : d.stacks 0 = familyCode G) (h1 : d.stacks 1 = mask)
    (h2 : d.stacks 2 = []) (h3 : d.stacks 3 = [])
    (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) :
    state d.regs (familyCode G) mask [] [] [] [] = d := by
  cases d
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm

theorem program_runsIn_from (G : Family) (mask : List Bool) (d : Data)
    (h0 : d.stacks 0 = familyCode G) (h1 : d.stacks 1 = mask)
    (h2 : d.stacks 2 = []) (h3 : d.stacks 3 = [])
    (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) :
    RunsIn program (bound G) (d.withPC (some program.entry))
      ((state (fun _ => false) (familyCode G) (mask.drop (G.headD []).length)
        (clauseCode (CoreMaskProgram.select mask (G.headD []))) [] [] []).withPC none) := by
  have h := program_runsIn G mask d.regs
  rwa [state_eq d G mask h0 h1 h2 h3 h4 h5] at h

theorem core_length_le (G : Family) (mask : List Bool) :
    (clauseCode (CoreMaskProgram.select mask (G.headD []))).length ≤ (familyCode G).length :=
  (CoreMaskProgram.selected_encoded_length_le mask (G.headD [])).trans (firstClause_length_le G)

theorem primitive_execution (G : Family) (mask : List Bool) (regs : Fin 4 → Bool) :
    Computation.RunsIn (primitive program).step (primitiveOverhead program * bound G)
      (primitiveCfg program
        ((state regs (familyCode G) mask [] [] [] []).withPC (some program.entry)))
      (primitiveCfg program
        ((state (fun _ => false) (familyCode G) (mask.drop (G.headD []).length)
          (clauseCode (CoreMaskProgram.select mask (G.headD []))) [] [] []).withPC none)) :=
  BitProgram.primitive_execution program (program_runsIn G mask regs)

end SubexponentialSAT.FirstClauseCoreProgram

end OAI.Algorithms
