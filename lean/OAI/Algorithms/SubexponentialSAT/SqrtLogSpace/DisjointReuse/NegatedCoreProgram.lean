import OAI.Algorithms.SubexponentialSAT.SubexpTautologyProgram
import OAI.Algorithms.SubexponentialSAT.ExecLiteralDedupProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

/-! Concrete negated singleton generation for the disjoint B child.
The fixed routine consumes a unary literal-record list on stack 0 and prepends
its negated singleton clauses to the encoded formula on stack 2. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram

open BitProgram StructuredCalls

abbrev Data := State 10 8
abbrev ports := ExecLiteralDedupProgram.ports
abbrev clauseCode := SubexpTautologyProgram.encodedClause

def formulaCode (F : List (List ℕ)) : List Bool :=
  Encoding.encodeList clauseCode F

def units (H : List ℕ) : List (List ℕ) :=
  H.reverse.map fun c => [SubexpFrontend.negateCode c]

def copyQueryProgram : Program 10 8 8 := StackRoutines.copyProgram 1 7 6 0 1
def copyQuery : Cmd 10 8 := .call copyQueryProgram
def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 1 7 d.stacks⟩

theorem copyQuery_eval (d : Data) (htmp : d.stacks 6 = []) :
    Eval copyQuery (7 * (d.stacks 1).length + 5) d (copied d) := by
  apply Eval.call
  simpa [copyQueryProgram, copied, StructuredProgram.State.withPC] using
    ListRegisterProgram.copy_run (r := 10) (s := 8) 1 7 6 0 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp

def seed : Cmd 10 8 := .seq (RecordPrograms.atom (.set 0 false))
  (RecordPrograms.atom (.push 3 0))

def seeded (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks 3 (false :: d.stacks 3)⟩

theorem seed_eval (d : Data) : Eval seed 2 d (seeded d) := by
  have h := (Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.set (r := 10) (s := 8) 0 false) d)).seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push 3 0)
      ((StructuredProgram.Atom.set 0 false).eval d)))
  simpa [seed, RecordPrograms.atom, seeded, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

def innerStack (i : Fin 4) : Fin 8 :=
  if i = 0 then 0 else if i = 1 then 6 else if i = 2 then 3 else 1

theorem innerStack_injective : Function.Injective innerStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [innerStack]

def innerProgram := ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram
  ExecLiteralDedupProgram.emitReg innerStack
def innerEmit : Cmd 10 8 := .call innerProgram

def innerResult (bits : List Bool) (d : Data) : Data :=
  ⟨Function.update (Function.update d.regs 7 true) 8 false,
    Function.update (Function.update d.stacks 1 []) 3
      (true :: (Encoding.frame bits ++ d.stacks 3))⟩

theorem innerEmit_eval (bits : List Bool) (d : Data)
    (hq : d.stacks 1 = bits.reverse) :
    Eval innerEmit (5 * bits.length + 7) d (innerResult bits d) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 7) (d.regs 8) (d.regs 9)
    (d.stacks 0) (d.stacks 6) (d.stacks 3) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 9)
    (d.stacks 0) (d.stacks 6) (true :: (Encoding.frame bits ++ d.stacks 3)) []
  have ha : embedState ExecLiteralDedupProgram.emitReg innerStack d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _
      ExecLiteralDedupProgram.emitReg_injective innerStack_injective
    · intro i
      fin_cases i <;> simp [a, ExecLiteralDedupProgram.emitReg,
        SubexpNormalizeProgram.filterState]
    · intro i _
      rfl
    · intro i
      fin_cases i <;> simp [a, innerStack, SubexpNormalizeProgram.filterState, hq]
    · intro i _
      rfl
  have hb : embedState ExecLiteralDedupProgram.emitReg innerStack d b = innerResult bits d := by
    apply embedState_eq_of_ports _ _ _ _ _
      ExecLiteralDedupProgram.emitReg_injective innerStack_injective
    · intro i
      fin_cases i <;> simp [b, innerResult, ExecLiteralDedupProgram.emitReg,
        SubexpNormalizeProgram.filterState]
    · intro i hi
      have h7 : i ≠ 7 := fun h => hi ⟨0, h.symm⟩
      have h8 : i ≠ 8 := fun h => hi ⟨1, h.symm⟩
      simp [innerResult, h7, h8]
    · intro i
      fin_cases i <;> simp [b, innerResult, innerStack,
        SubexpNormalizeProgram.filterState]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨3, h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨2, h.symm⟩
      simp [innerResult, h1, h3]
  have he := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram
    ExecLiteralDedupProgram.emitReg innerStack d
    ExecLiteralDedupProgram.emitReg_injective innerStack_injective
    (SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 6)
      (d.stacks 3) (d.regs 7) (d.regs 8) (d.regs 9))
  change Eval innerEmit (5 * bits.length + 7)
    (embedState _ _ d a) (embedState _ _ d b) at he
  simpa only [ha, hb] using he

def transferClauseProgram : Program 10 8 4 := StackRoutines.transferProgram 3 1 0 1
def transferClause : Cmd 10 8 := .call transferClauseProgram
def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 3 1 d.stacks⟩

theorem transferClause_eval (d : Data) :
    Eval transferClause (3 * (d.stacks 3).length + 3) d (transferred d) := by
  apply Eval.call
  simpa [transferClauseProgram, transferred, StructuredProgram.State.withPC] using
    ListRegisterProgram.transfer_run (r := 10) (s := 8) 3 1 0 1
      (by decide) (by decide) d.regs d.stacks

def select : Cmd 10 8 := RecordPrograms.atom (.set 9 true)
def selected (d : Data) : Data := ⟨Function.update d.regs 9 true, d.stacks⟩

theorem select_eval (d : Data) : Eval select 1 d (selected d) := by
  simpa [select, RecordPrograms.atom, selected, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using
    Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 9 true) d)

def callback : Cmd 10 8 := .seq copyQuery (.seq (ExecCNFSubset.clear 1)
  (.seq SubexpTautologyProgram.negateQuery (.seq (ExecCNFSubset.clear 7)
    (.seq seed (.seq innerEmit (.seq transferClause (.seq select
      ExecLiteralDedupProgram.emitCall)))))))

theorem callback_eval (c : ℕ) (d : Data)
    (hquery : d.stacks 1 = (Encoding.encodeNat c).reverse)
    (hclean : ExecLiteralDedupProgram.Clean d) :
    ∃ t ≤ 200 * ((Encoding.encodeNat c).length + 1), ∃ e : Data,
      Eval callback t d e ∧ ExecLiteralDedupProgram.Clean e ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 1 = [] ∧
      e.stacks 2 = true :: (Encoding.frame (clauseCode [SubexpFrontend.negateCode c]) ++
        d.stacks 2) ∧ e.regs 7 = false ∧ e.regs 8 = true ∧ e.regs 9 = false := by
  rcases hclean with ⟨h3, h4, h5, h6, h7⟩
  let a := ExecCNFSubset.cleared 1 (copied d)
  have ha7 : a.stacks 7 = (Encoding.encodeNat c).reverse := by
    simp [a, StackRoutines.clearStacks, copied,
      StackRoutines.copyStacks, hquery, h7]
  obtain ⟨b, hb, hb1, hb0, hb2, hb3, hb4, hb5, hb6, hb7, _, _, _⟩ :=
    SubexpTautologyProgram.negateQuery_eval c a ha7
      (by simp [a, StackRoutines.clearStacks])
      (by simp [a, StackRoutines.clearStacks, copied,
        StackRoutines.copyStacks, h5])
      (by simp [a, StackRoutines.clearStacks, copied,
        StackRoutines.copyStacks, h6])
  let q := seeded (ExecCNFSubset.cleared 7 b)
  let bits := Encoding.encodeNat (SubexpFrontend.negateCode c)
  let w := innerResult bits q
  let z := selected (transferred w)
  have hq1 : q.stacks 1 = bits.reverse := by
    simpa [q, bits, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks] using hb1
  have hq3 : q.stacks 3 = [false] := by
    simp [q, seeded, StackRoutines.clearStacks, hb3,
      a, copied, StackRoutines.copyStacks, h3]
  have hw3 : w.stacks 3 = clauseCode [SubexpFrontend.negateCode c] := by
    simp [w, innerResult, hq3, clauseCode, SubexpTautologyProgram.encodedClause,
      Encoding.encodeList, bits]
  have hz1 : z.stacks 1 = (clauseCode [SubexpFrontend.negateCode c]).reverse := by
    have hw1 : w.stacks 1 = [] := by simp [w, innerResult]
    simpa [z, selected, transferred, StackRoutines.transferStacks, hw1] using
      congrArg List.reverse hw3
  obtain ⟨e, he, he0, he1, he2, he3, he4, he5, he6, he7, hr7, hr8, hr9⟩ :=
    ExecLiteralDedupProgram.emitCall_eval true (clauseCode [SubexpFrontend.negateCode c]) z
      hz1 (by simp [z, selected])
  let t := (7 * (d.stacks 1).length + 5) +
    ((2 * ((copied d).stacks 1).length + 3) +
    (SubexpNegatedQueryProgram.steps c + ((2 * (b.stacks 7).length + 3) +
    (2 + ((5 * bits.length + 7) + ((3 * (w.stacks 3).length + 3) +
    (1 + (SubexpNormalizeProgram.emitIfSelectedSteps true
      (clauseCode [SubexpFrontend.negateCode c]) + 1))))))))
  refine ⟨t, ?_, e, ?_, ?_, ?_, he1, ?_, hr7, hr8, hr9⟩
  · have hn := SubexpNegatedQueryProgram.steps_le c
    have hbits : bits.length ≤ (Encoding.encodeNat c).length + 1 := by
      dsimp [bits]
      simpa only [Encoding.length_encodeNat] using
        Nat.add_le_add_right (SubexpNegatedQueryProgram.negateCode_le c) 1
    have hc : (clauseCode [SubexpFrontend.negateCode c]).length = 2 * bits.length + 3 := by
      simp [clauseCode, SubexpTautologyProgram.encodedClause, bits]
    have hcopyLen : ((copied d).stacks 1).length = (Encoding.encodeNat c).length := by
      simp [copied, StackRoutines.copyStacks, hquery]
    simp only [t, hquery, hcopyLen, hb7, ha7, hw3, List.length_reverse,
      SubexpNormalizeProgram.emitIfSelectedSteps, ite_true]
    rw [hc]
    omega
  · exact (copyQuery_eval d h6).seq ((ExecCNFSubset.clear_eval 1 (copied d)).seq
      (hb.seq ((ExecCNFSubset.clear_eval 7 b).seq ((seed_eval _).seq
        ((innerEmit_eval bits q hq1).seq ((transferClause_eval w).seq
          ((select_eval (transferred w)).seq he)))))))
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [z, selected, transferred, StackRoutines.transferStacks] using he3
    · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
        q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb4,
        a, copied, StackRoutines.copyStacks, h4] using he4
    · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
        q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb5] using he5
    · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
        q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb6] using he6
    · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
        q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks] using he7
  · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
      q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb0,
      a, copied, StackRoutines.copyStacks] using he0
  · simpa [z, selected, transferred, StackRoutines.transferStacks, w, innerResult,
      q, seeded, ExecCNFSubset.cleared, StackRoutines.clearStacks, hb2,
      a, copied, StackRoutines.copyStacks] using he2

def unitCode (bits : List Bool) : List Bool :=
  match Encoding.readNat bits with
  | none => []
  | some (c, _) => clauseCode [SubexpFrontend.negateCode c]

@[simp] theorem unitCode_encodeNat (c : ℕ) :
    unitCode (Encoding.encodeNat c) = clauseCode [SubexpFrontend.negateCode c] := by
  simp [unitCode]

theorem callback_contract :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (fun bits => 200 * (bits.length + 1)) ExecLiteralDedupProgram.Clean
      (fun bits a b => b.stacks 2 = true :: (Encoding.frame (unitCode bits) ++ a.stacks 2))
      (fun bits => ∃ c, bits = Encoding.encodeNat c) := by
  intro bits tail base hbits hbase
  obtain ⟨c, rfl⟩ := hbits
  let d := RecordPrograms.state ports base false true false tail (Encoding.encodeNat c).reverse
  have hd1 : d.stacks 1 = (Encoding.encodeNat c).reverse := by
    simp [d, RecordPrograms.state]
  have hd : ExecLiteralDedupProgram.Clean d := by
    simpa [d] using hbase
  obtain ⟨t, ht, e, he, hclean, h0, h1, h2, h7, h8, h9⟩ := callback_eval c d hd1 hd
  have h0' : e.stacks 0 = tail := by
    simpa [d, ports, RecordPrograms.state, ExecLiteralDedupProgram.ports] using h0
  have hend : RecordPrograms.state ports e false true false tail [] = e :=
    RecordPrograms.state_eq_self ports e _ _ _ _ _ h7 h8 h9 h0' h1
  refine ⟨t, e, ht, hclean, ?_, ?_⟩
  · simpa [d] using h2
  · rw [hend]
    exact he

theorem fold_units (H : List ℕ) (F : List (List ℕ)) :
    (H.map Encoding.encodeNat).foldl
      (fun acc bits => true :: (Encoding.frame (unitCode bits) ++ acc)) (formulaCode F) =
      formulaCode (units H ++ F) := by
  induction H generalizing F with
  | nil => rfl
  | cons c H ih =>
      simp only [List.map_cons, List.foldl_cons, unitCode_encodeNat]
      change (H.map Encoding.encodeNat).foldl _
        (formulaCode ([SubexpFrontend.negateCode c] :: F)) = _
      rw [ih]
      simp [units, List.reverse_cons, List.map_append, List.append_assoc]

def command : Cmd 10 8 := RecordPrograms.iterate ports callback
def program := compiled command 0 2

theorem command_eval (H : List ℕ) (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = clauseCode H) (houtput : d.stacks 2 = formulaCode F)
    (hpayload : d.stacks 1 = []) (hclean : ExecLiteralDedupProgram.Clean d) :
    ∃ t, t + 1 ≤ 417 * ((clauseCode H).length + 1) ∧ ∃ e : Data,
      Eval command t d e ∧ e.stacks 2 = formulaCode (units H ++ F) ∧
      (∀ i : Fin 8, i ≠ 2 → e.stacks i = []) := by
  let records := H.map Encoding.encodeNat
  have hrecords : ∀ bits ∈ records, ∃ c, bits = Encoding.encodeNat c := by
    intro bits hbits
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hbits
    exact ⟨c, rfl⟩
  have hencode : Encoding.encodeList id records = clauseCode H :=
    (SubexpTautologyProgram.encodedClause_records H).symm
  have hstart : RecordPrograms.state ports d (d.regs 7) (d.regs 8) (d.regs 9)
      (Encoding.encodeList id records ++ []) [] = d :=
    RecordPrograms.state_eq_self ports d _ _ _ _ _ rfl rfl rfl
      (by simpa only [List.append_nil, hencode] using hsource) hpayload
  obtain ⟨t, next, ht, hn, hvisits, hrun⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (fun bits => 200 * (bits.length + 1))
    ExecLiteralDedupProgram.Clean
    (fun bits a b => b.stacks 2 = true :: (Encoding.frame (unitCode bits) ++ a.stacks 2))
    (fun bits => ∃ c, bits = Encoding.encodeNat c) callback_contract
    records [] d hrecords hclean (d.regs 7) (d.regs 8) (d.regs 9)
  have hunread : RecordPrograms.unread (fun _ => false) records [] = [] := by
    induction records with
    | nil => rfl
    | cons b rest ih => simp [RecordPrograms.unread, ih]
  have hany : records.any (fun _ => false) = false := by simp
  have hfold := hvisits.fold_of_false (fun _ _ => rfl) (fun a => a.stacks 2)
    (fun acc bits => true :: (Encoding.frame (unitCode bits) ++ acc))
    (fun _ _ _ h => h)
  have hout : next.stacks 2 = formulaCode (units H ++ F) := by
    rw [houtput] at hfold
    exact hfold.trans (fold_units H F)
  let e := RecordPrograms.state ports next false true false [] []
  have hb := RecordPrograms.program_budget_le_input
    (fun bits => 200 * (bits.length + 1)) records 200 200 (by
      intro bits _
      omega)
  change 4 + RecordPrograms.budget (fun bits => 200 * (bits.length + 1)) records ≤
    417 * ((Encoding.encodeList id records).length + 1) at hb
  rw [hencode] at hb
  refine ⟨t, by omega, e, ?_, ?_, ?_⟩
  · simpa only [hstart, hunread, hany, command] using hrun
  · simpa [e] using hout
  · rcases hn with ⟨h3, h4, h5, h6, h7⟩
    intro i hi
    fin_cases i <;> simp_all [e, ports, RecordPrograms.state, ExecLiteralDedupProgram.ports]

theorem program_runsIn (H : List ℕ) (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = clauseCode H) (houtput : d.stacks 2 = formulaCode F)
    (hpayload : d.stacks 1 = []) (hclean : ExecLiteralDedupProgram.Clean d) :
    ∃ e : Data, e.stacks 2 = formulaCode (units H ++ F) ∧
      (∀ i : Fin 8, i ≠ 2 → e.stacks i = []) ∧
      RunsIn program (417 * ((clauseCode H).length + 1))
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨t, ht, e, he, hout, hscratch⟩ := command_eval H F d hsource houtput hpayload hclean
  exact ⟨e, hout, hscratch, t + 1, ht, compiled_halt_trace he 0 2⟩

/-- This polynomial-time phase bounds every intermediate stack, including scratch.
The primitive tape-span transfer is a separate compiler theorem. -/
theorem prefix_stackBits_le (H : List ℕ) (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = clauseCode H) (houtput : d.stacks 2 = formulaCode F)
    (hpayload : d.stacks 1 = []) (hclean : ExecLiteralDedupProgram.Clean d)
    {t : ℕ} {c : Cfg 10 8 (size command + 1)}
    (ht : t ≤ 417 * ((clauseCode H).length + 1))
    (htrace : Trace program t (d.withPC (some program.entry)) c) :
    dataBits c ≤ (formulaCode F).length + 418 * ((clauseCode H).length + 1) := by
  have hbits := trace_dataBits program htrace
  have hd : dataBits (d.withPC (some program.entry)) =
      (clauseCode H).length + (formulaCode F).length := by
    rcases hclean with ⟨h3, h4, h5, h6, h7⟩
    simp [dataBits, stackBits, Fin.sum_univ_succ,
      hsource, houtput, hpayload, h3, h4, h5, h6, h7]
  rw [hd] at hbits
  omega

theorem output_length_le (H : List ℕ) (F : List (List ℕ)) :
    (formulaCode (units H ++ F)).length ≤
      (formulaCode F).length + 8 * (clauseCode H).length := by
  induction H generalizing F with
  | nil => simp [units]
  | cons c H ih =>
      have hneg : (Encoding.encodeNat (SubexpFrontend.negateCode c)).length ≤
          (Encoding.encodeNat c).length + 1 := by
        simpa only [Encoding.length_encodeNat] using
          Nat.add_le_add_right (SubexpNegatedQueryProgram.negateCode_le c) 1
      have hrec := ih ([SubexpFrontend.negateCode c] :: F)
      have heq : units (c :: H) ++ F = units H ++ ([SubexpFrontend.negateCode c] :: F) := by
        simp [units, List.reverse_cons, List.map_append, List.append_assoc]
      rw [heq]
      simp only [formulaCode, Encoding.length_encodeList_cons] at hrec ⊢
      simp only [clauseCode, SubexpTautologyProgram.encodedClause,
        Encoding.length_encodeList_cons, Encoding.length_encodeList_nil] at hrec ⊢
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram
