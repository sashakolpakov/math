import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleSplit
import OAI.Algorithms.SubexponentialSAT.ExecSelectedFamilyProgram
import OAI.Algorithms.SubexponentialSAT.TupleGuardProgram
import OAI.Algorithms.SubexponentialSAT.FirstClauseCoreProgram

namespace OAI.Algorithms

/-!
# Concrete preparation of a sunflower candidate

This fixed program splits a preserved mask-first tuple, checks its binary
indices, gathers the selected clauses, and selects a core from the first
gathered clause. Every stage calls an actual finite Boolean-stack program.
The input formula, tuple, limit, and all unrelated stacks are preserved.
-/

namespace SubexponentialSAT.CandidatePrepareProgram

open BitProgram StructuredCalls

abbrev Clause := List (List Bool)
abbrev Formula := List Clause
abbrev Data := State 32 32
abbrev Code := Cmd 32 32

def clauseCode (C : Clause) := Encoding.encodeList id C
def formulaCode (F : Formula) := Encoding.encodeList clauseCode F
def tupleCode (words : List (List Bool)) := Encoding.encodeList id words
def selected (F : Formula) (words : List (List Bool)) :=
  (ExecSelectedFamilyProgram.selectedClauses F words).reverse
def core (F : Formula) (mask : List Bool) (words : List (List Bool)) :=
  CoreMaskProgram.select mask ((selected F words).headD [])
def valid (limit : List Bool) (words : List (List Bool)) :=
  TupleGuardProgram.goodFrom limit none words

def WorkEmpty (d : Data) : Prop :=
  (∀ i : Fin 7, d.stacks (Fin.castAdd 25 i) = []) ∧
  d.stacks 8 = [] ∧ d.stacks 13 = [] ∧ d.stacks 22 = [] ∧
  d.stacks 23 = [] ∧ d.stacks 24 = [] ∧ d.stacks 25 = [] ∧ d.stacks 26 = []

def Ready (F : Formula) (mask limit : List Bool) (words : List (List Bool))
    (d : Data) : Prop :=
  d.stacks 16 = formulaCode F ∧ d.stacks 17 = tupleCode (mask :: words) ∧
  d.stacks 19 = limit ∧ WorkEmpty d

def guardReg (i : Fin 13) : Fin 32 := Fin.castAdd 19 i
def guardStack : Fin 9 → Fin 32 := ![23, 0, 1, 19, 2, 3, 4, 5, 6]
theorem guardReg_injective : Function.Injective guardReg := Fin.castAdd_injective 13 19
theorem guardStack_injective : Function.Injective guardStack := by decide

def guard : Code := .seq
  (.call (ProgramLinking.liftProgram TupleGuardProgram.program guardReg guardStack))
  (RecordPrograms.atom (.copy 30 10))

theorem guard_eval (limit : List Bool) (words : List (List Bool)) (d : Data)
    (ht : d.stacks 23 = tupleCode words) (hl : d.stacks 19 = limit)
    (hw : ∀ i : Fin 7, d.stacks (Fin.castAdd 25 i) = []) :
    ∃ n ≤ TupleGuardProgram.bound limit words + 1, ∃ e : Data,
      Eval guard n d e ∧ e.stacks = d.stacks ∧ e.regs 30 = valid limit words := by
  let a := projectState guardReg guardStack d
  have haw : TupleGuardProgram.workEmpty a := by
    rcases (show d.stacks 0 = [] ∧ d.stacks 1 = [] ∧ d.stacks 2 = [] ∧
        d.stacks 3 = [] ∧ d.stacks 4 = [] ∧ d.stacks 5 = [] ∧ d.stacks 6 = [] from
      ⟨hw 0, hw 1, hw 2, hw 3, hw 4, hw 5, hw 6⟩) with
      ⟨h0, h1, h2, h3, h4, h5, h6⟩
    simpa [TupleGuardProgram.workEmpty, a, projectState, guardStack] using
      And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5 h6)))))
  obtain ⟨b, ⟨n, hn, htrace⟩, hb0, hb3, hbw, hb10⟩ :=
    TupleGuardProgram.program_runsIn limit words a ht hl haw
  have hba : b.stacks = a.stacks := by
    rcases hbw with ⟨hb1, hb2, hb4, hb5, hb6, hb7, hb8⟩
    rcases haw with ⟨ha1, ha2, ha4, ha5, ha6, ha7, ha8⟩
    funext i
    fin_cases i
    · exact hb0.trans ht.symm
    · exact hb1.trans ha1.symm
    · exact hb2.trans ha2.symm
    · exact hb3.trans hl.symm
    · exact hb4.trans ha4.symm
    · exact hb5.trans ha5.symm
    · exact hb6.trans ha6.symm
    · exact hb7.trans ha7.symm
    · exact hb8.trans ha8.symm
  let c := embedState guardReg guardStack d b
  have hc : Eval (.call (ProgramLinking.liftProgram TupleGuardProgram.program
      guardReg guardStack)) n d c :=
    eval_call_from_state _ _ _ _ guardReg_injective guardStack_injective htrace
  have hcs : c.stacks = d.stacks := by
    funext i
    classical
    by_cases hi : ∃ j, guardStack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack _ _ _ _ guardStack_injective j).trans
        (congrFun hba j)
    · exact embedState_stack_frame _ _ _ _ i hi
  have hc10 : c.regs 10 = valid limit words :=
    (embedState_register _ _ _ _ guardReg_injective 10).trans hb10
  let e := (StructuredProgram.Atom.copy (r := 32) (s := 32) 30 10).eval c
  refine ⟨n + 1, by omega, e, Eval.seq hc (.base (.atom _ _)), hcs, ?_⟩
  simpa [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using hc10

def smallReg (i : Fin 4) : Fin 32 := Fin.castAdd 28 i
theorem smallReg_injective : Function.Injective smallReg := Fin.castAdd_injective 4 28
def gatherStack : Fin 10 → Fin 32 := ![16, 0, 13, 1, 2, 3, 4, 23, 5, 6]
theorem gatherStack_injective : Function.Injective gatherStack := by decide

def initGather : Code :=
  .seq (RecordPrograms.atom (.set 0 false))
    (.seq (RecordPrograms.atom (.set 1 false))
      (.seq (RecordPrograms.atom (.set 2 false))
        (.seq (RecordPrograms.atom (.set 3 false)) (RecordPrograms.atom (.push 13 0)))))

def initialized (d : Data) : Data :=
  (StructuredProgram.Atom.push 13 0).eval
    ((StructuredProgram.Atom.set 3 false).eval
      ((StructuredProgram.Atom.set 2 false).eval
        ((StructuredProgram.Atom.set 1 false).eval
          ((StructuredProgram.Atom.set 0 false).eval d))))

theorem initialize_eval (d : Data) : Eval initGather 5 d (initialized d) :=
  Eval.seq (.base (.atom _ _)) (Eval.seq (.base (.atom _ _))
    (Eval.seq (.base (.atom _ _)) (Eval.seq (.base (.atom _ _)) (.base (.atom _ _)))))

theorem initialized_stacks (d : Data) :
    (initialized d).stacks = Function.update d.stacks 13 (false :: d.stacks 13) := by
  simp [initialized, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr]

theorem initialized_regs (d : Data) (i : Fin 4) :
    (initialized d).regs (smallReg i) = false := by
  fin_cases i <;> simp [initialized, smallReg, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]

theorem initialized_flag (d : Data) : (initialized d).regs 30 = d.regs 30 := by
  simp [initialized, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr]

def gather : Code := .seq initGather
  (.call (ProgramLinking.liftProgram ExecSelectedFamilyProgram.program smallReg gatherStack))

theorem gather_eval (F : Formula) (words : List (List Bool)) (d : Data)
    (hF : d.stacks 16 = formulaCode F) (ht : d.stacks 23 = tupleCode words)
    (ho : d.stacks 13 = []) (hw : ∀ i : Fin 7, d.stacks (Fin.castAdd 25 i) = []) :
    ∃ n ≤ 128 * ((formulaCode F).length + 1) * ((tupleCode words).length + 1) + 5,
    ∃ e : Data, Eval gather n d e ∧
      e.stacks = Function.update d.stacks 13 (formulaCode (selected F words)) ∧
      e.regs 30 = d.regs 30 := by
  let a := initialized d
  have ha : projectState smallReg gatherStack a =
      ExecSelectedFamilyProgram.baseState (formulaCode F) (tupleCode words) [false] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> exact initialized_regs d _
    · funext i
      have h0 : d.stacks 0 = [] := hw 0
      have h1 : d.stacks 1 = [] := hw 1
      have h2 : d.stacks 2 = [] := hw 2
      have h3 : d.stacks 3 = [] := hw 3
      have h4 : d.stacks 4 = [] := hw 4
      have h5 : d.stacks 5 = [] := hw 5
      have h6 : d.stacks 6 = [] := hw 6
      fin_cases i <;> simp [ a, initialized_stacks, gatherStack,
        hF, ht, ho, h0, h1, h2, h3, h4, h5, h6]
  obtain ⟨n, hn, htrace⟩ := ExecSelectedFamilyProgram.clause_family_runs F words
  change n ≤ 128 * ((formulaCode F).length + 1) * ((tupleCode words).length + 1) at hn
  let b := ExecSelectedFamilyProgram.baseState (formulaCode F) (tupleCode words)
    (formulaCode (selected F words))
  have hb : Trace ExecSelectedFamilyProgram.program n
      ((projectState smallReg gatherStack a).withPC (some ExecSelectedFamilyProgram.program.entry))
      (b.withPC none) := by
    rw [ha]
    exact htrace
  let e := embedState smallReg gatherStack a b
  have he := eval_call_from_state _ smallReg gatherStack a
    smallReg_injective gatherStack_injective hb
  refine ⟨5 + n, by omega, e, Eval.seq (initialize_eval d) he, ?_, ?_⟩
  · funext i
    classical
    by_cases hi : ∃ j, gatherStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [show e.stacks (gatherStack j) = b.stacks j from
        embedState_stack _ _ _ _ gatherStack_injective j]
      have h0 : d.stacks 0 = [] := hw 0
      have h1 : d.stacks 1 = [] := hw 1
      have h2 : d.stacks 2 = [] := hw 2
      have h3 : d.stacks 3 = [] := hw 3
      have h4 : d.stacks 4 = [] := hw 4
      have h5 : d.stacks 5 = [] := hw 5
      have h6 : d.stacks 6 = [] := hw 6
      fin_cases j <;> simp [b, gatherStack, ExecSelectedFamilyProgram.baseState,
        ExecSelectedFamilyProgram.stage, hF, ht, h0, h1, h2, h3, h4, h5, h6]
    · have h13 : i ≠ 13 := by
        intro h
        apply hi
        exact ⟨2, h.symm⟩
      rw [show e.stacks i = a.stacks i from embedState_stack_frame _ _ _ _ i hi]
      simp [a, initialized_stacks, h13]
  · exact (embedState_register_frame _ _ _ _ 30 (by decide)).trans (initialized_flag d)

def coreStack : Fin 6 → Fin 32 := ![13, 22, 8, 0, 1, 2]
theorem coreStack_injective : Function.Injective coreStack := by decide

def chooseCore : Code :=
  .call (ProgramLinking.liftProgram FirstClauseCoreProgram.program smallReg coreStack)

theorem chooseCore_eval (G : Formula) (mask : List Bool) (d : Data)
    (hG : d.stacks 13 = formulaCode G) (hm : d.stacks 22 = mask)
    (h8 : d.stacks 8 = []) (h0 : d.stacks 0 = [])
    (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = []) :
    ∃ n ≤ FirstClauseCoreProgram.bound G, ∃ e : Data,
      Eval chooseCore n d e ∧
      e.stacks = Function.update
        (Function.update d.stacks 22 (mask.drop (G.headD []).length))
        8 (clauseCode (CoreMaskProgram.select mask (G.headD []))) ∧
      e.regs 30 = d.regs 30 := by
  let a := projectState smallReg coreStack d
  obtain ⟨n, hn, htrace⟩ := FirstClauseCoreProgram.program_runsIn_from G mask a
    hG hm h8 h0 h1 h2
  let b := FirstClauseCoreProgram.state (fun _ => false) (formulaCode G)
    (mask.drop (G.headD []).length)
    (clauseCode (CoreMaskProgram.select mask (G.headD []))) [] [] []
  let e := embedState smallReg coreStack d b
  have he := eval_call_from_state _ smallReg coreStack d
    smallReg_injective coreStack_injective htrace
  refine ⟨n, hn, e, he, ?_, ?_⟩
  · funext i
    classical
    by_cases hi : ∃ j, coreStack j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [show e.stacks (coreStack j) = b.stacks j from
        embedState_stack _ _ _ _ coreStack_injective j]
      fin_cases j <;> simp [b, coreStack, FirstClauseCoreProgram.state, hG, h0, h1, h2]
    · have h8' : i ≠ 8 := by intro h; apply hi; exact ⟨2, h.symm⟩
      have h22' : i ≠ 22 := by intro h; apply hi; exact ⟨1, h.symm⟩
      rw [show e.stacks i = d.stacks i from embedState_stack_frame _ _ _ _ i hi]
      simp [h8', h22']
  · exact embedState_register_frame _ _ _ _ 30 (by decide)

def cleanup : Code := .seq (ExecCNFTupleSplit.clear 22) (ExecCNFTupleSplit.clear 23)
def cleaned (d : Data) := ExecCNFTupleSplit.cleared 23 (ExecCNFTupleSplit.cleared 22 d)

theorem cleanup_eval (d : Data) :
    Eval cleanup (2 * (d.stacks 22).length + 2 * (d.stacks 23).length + 6) d (cleaned d) := by
  have h := Eval.seq (ExecCNFTupleSplit.clear_eval 22 d)
    (ExecCNFTupleSplit.clear_eval 23 (ExecCNFTupleSplit.cleared 22 d))
  change Eval cleanup ((2 * (d.stacks 22).length + 3) +
    (2 * (d.stacks 23).length + 3)) d (cleaned d) at h
  convert h using 1 ; omega

theorem cleaned_stacks (d : Data) : (cleaned d).stacks =
    Function.update (Function.update d.stacks 22 []) 23 [] := rfl

theorem cleaned_flag (d : Data) : (cleaned d).regs 30 = d.regs 30 := by
  simp [cleaned, ExecCNFTupleSplit.cleared, readRegs]

def prepareValid : Code := .seq gather chooseCore
def command : Code := .seq ExecCNFTupleSplit.command
  (.seq guard (.seq (.ite 30 prepareValid (.base .skip)) cleanup))
def program := compiled command 17 13

def bound (F : Formula) (mask limit : List Bool) (words : List (List Bool)) : ℕ :=
  ExecCNFTupleSplit.cost mask words + TupleGuardProgram.bound limit words +
  128 * ((formulaCode F).length + 1) * ((tupleCode words).length + 1) +
  FirstClauseCoreProgram.bound (selected F words) +
  2 * mask.length + 2 * (tupleCode words).length + 20

def outputStacks (F : Formula) (mask limit : List Bool) (words : List (List Bool))
    (d : Data) : Fin 32 → List Bool :=
  Function.update (Function.update d.stacks 13
    (if valid limit words then formulaCode (selected F words) else []))
    8 (if valid limit words then clauseCode (core F mask words) else [])

theorem split_eval (mask : List Bool) (words : List (List Bool)) (d : Data)
    (h : ExecCNFTupleSplit.Ready mask words d) :
    ∃ e : Data, Eval ExecCNFTupleSplit.command (ExecCNFTupleSplit.cost mask words) d e ∧
      e.stacks = Function.update (Function.update d.stacks 22 mask) 23 (tupleCode words) := by
  obtain ⟨e, he, hm, ht, h24, hf⟩ := ExecCNFTupleSplit.command_eval mask words d h
  refine ⟨e, he, ?_⟩
  funext i
  by_cases hi22 : i = 22
  · subst i
    simpa using hm
  by_cases hi23 : i = 23
  · subst i
    simpa [tupleCode] using ht
  by_cases hi24 : i = 24
  · subst i
    simpa using h24.trans h.2.2.2.1.symm
  simpa [hi22, hi23] using hf i hi22 hi23 hi24

/-- Complete preparation, including both branches and deletion of parsed
tuple copies. Only the two output stacks differ from the original state. -/
theorem command_eval (F : Formula) (mask limit : List Bool) (words : List (List Bool))
    (d : Data) (h : Ready F mask limit words d) :
    ∃ n, n + 1 ≤ bound F mask limit words ∧ ∃ e : Data,
      Eval command n d e ∧ e.stacks = outputStacks F mask limit words d ∧
      e.regs 30 = valid limit words := by
  rcases h with ⟨hF, ht, hl, hw, h8, h13, h22, h23, h24, h25, h26⟩
  obtain ⟨a, ha, has⟩ := split_eval mask words d ⟨ht, h22, h23, h24, h25, h26⟩
  have haw : ∀ i : Fin 7, a.stacks (Fin.castAdd 25 i) = [] := by
    intro i
    fin_cases i
    · simpa [has] using hw 0
    · simpa [has] using hw 1
    · simpa [has] using hw 2
    · simpa [has] using hw 3
    · simpa [has] using hw 4
    · simpa [has] using hw 5
    · simpa [has] using hw 6
  have hat : a.stacks 23 = tupleCode words := by simp [has]
  have hal : a.stacks 19 = limit := by simp [has, hl]
  obtain ⟨n, hn, b, hb, hbs, hbg⟩ := guard_eval limit words a hat hal haw
  have hbw : ∀ i : Fin 7, b.stacks (Fin.castAdd 25 i) = [] := by
    simpa only [hbs] using haw
  cases hv : valid limit words with
  | false =>
    have hbranch : Eval (.ite 30 prepareValid (.base .skip)) 1 b b :=
      Eval.ite_false (hbg.trans hv) (.base (.skip b))
    have hclean := cleanup_eval b
    have hb22 : b.stacks 22 = mask := by simp [hbs, has]
    have hb23 : b.stacks 23 = tupleCode words := by simp [hbs, has]
    refine ⟨ExecCNFTupleSplit.cost mask words +
      (n + (1 + (2 * (b.stacks 22).length + 2 * (b.stacks 23).length + 6))),
      ?_, cleaned b, Eval.seq ha (Eval.seq hb (Eval.seq hbranch hclean)), ?_, ?_⟩
    · rw [hb22, hb23]
      unfold bound
      omega
    · funext i
      fin_cases i <;> simp [cleaned_stacks, outputStacks, hbs, has, hv,
        h8, h13, h22, h23]
    · exact (cleaned_flag b).trans (hbg.trans hv)
  | true =>
    have hbF : b.stacks 16 = formulaCode F := by simp [hbs, has, hF]
    have hbt : b.stacks 23 = tupleCode words := by simp [hbs, has]
    have hb13 : b.stacks 13 = [] := by simp [hbs, has, h13]
    obtain ⟨g, hg, c, hc, hcs, hcg⟩ := gather_eval F words b hbF hbt hb13 hbw
    have hcG : c.stacks 13 = formulaCode (selected F words) := by simp [hcs]
    have hcm : c.stacks 22 = mask := by simp [hcs, hbs, has]
    have hc8 : c.stacks 8 = [] := by simp [hcs, hbs, has, h8]
    have hc0 : c.stacks 0 = [] := by simpa [hcs] using hbw 0
    have hc1 : c.stacks 1 = [] := by simpa [hcs] using hbw 1
    have hc2 : c.stacks 2 = [] := by simpa [hcs] using hbw 2
    obtain ⟨q, hq, e, he, hes, heg⟩ :=
      chooseCore_eval (selected F words) mask c hcG hcm hc8 hc0 hc1 hc2
    have hbranch : Eval (.ite 30 prepareValid (.base .skip)) (g + q + 1) b e :=
      Eval.ite_true (hbg.trans hv) (Eval.seq hc he)
    have he22 : e.stacks 22 = mask.drop ((selected F words).headD []).length := by
      simp [hes]
    have he23 : e.stacks 23 = tupleCode words := by simp [hes, hcs, hbs, has]
    refine ⟨ExecCNFTupleSplit.cost mask words +
      (n + ((g + q + 1) + (2 * (e.stacks 22).length + 2 * (e.stacks 23).length + 6))),
      ?_, cleaned e, Eval.seq ha (Eval.seq hb (Eval.seq hbranch (cleanup_eval e))), ?_, ?_⟩
    · rw [he22, he23]
      simp only [List.length_drop]
      unfold bound
      omega
    · funext i
      fin_cases i <;> simp [cleaned_stacks, outputStacks, hes, hcs, hbs, has,
        hv, core, h22, h23]
    · exact (cleaned_flag e).trans (heg.trans (hcg.trans (hbg.trans hv)))

theorem program_runsIn (F : Formula) (mask limit : List Bool) (words : List (List Bool))
    (d : Data) (h : Ready F mask limit words d) :
    ∃ e : Data, RunsIn program (bound F mask limit words)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = outputStacks F mask limit words d ∧ e.regs 30 = valid limit words := by
  obtain ⟨n, hn, e, he, hs, hg⟩ := command_eval F mask limit words d h
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 17 13⟩, hs, hg⟩

theorem primitive_execution (F : Formula) (mask limit : List Bool)
    (words : List (List Bool)) (d : Data) (h : Ready F mask limit words d) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * bound F mask limit words)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks = outputStacks F mask limit words d ∧ e.regs 30 = valid limit words := by
  obtain ⟨e, he, hs, hg⟩ := program_runsIn F mask limit words d h
  exact ⟨e, BitProgram.primitive_execution program he, hs, hg⟩

theorem valid_iff (limit : List Bool) (words : List (List Bool)) :
    valid limit words = true ↔
      (∀ bits ∈ words, BinaryArithmetic.toNat bits < BinaryArithmetic.toNat limit) ∧
      words.Pairwise (fun x y => BinaryArithmetic.toNat x < BinaryArithmetic.toNat y) :=
  TupleGuardProgram.goodFrom_none_iff limit words

theorem outputStacks_frame (F : Formula) (mask limit : List Bool) (words : List (List Bool))
    (d : Data) (i : Fin 32) (h8 : i ≠ 8) (h13 : i ≠ 13) :
    outputStacks F mask limit words d i = d.stacks i := by
  simp [outputStacks, h8, h13]

end SubexponentialSAT.CandidatePrepareProgram

end OAI.Algorithms
