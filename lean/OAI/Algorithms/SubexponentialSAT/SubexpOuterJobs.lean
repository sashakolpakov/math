import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExtractionHost
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpExponentController
import OAI.Algorithms.SubexponentialSAT.SubexpQueryOrder

namespace OAI.Algorithms

/-! A concrete outer moment loop.  Its source subroutine is an actual fixed
command; the separate contract records the input/output theorem needed from
the per-exponent weight and source constructors. -/

namespace SubexponentialSAT.SubexpOuterJobs

open BitProgram StructuredCalls

abbrev Data := SubexpExtractionHost.Data
abbrev Code := SubexpExtractionHost.Code

def ports : RecordPrograms.Ports 16 128 where
  tag := 13
  present := 14
  found := 15
  source := 110
  payload := 111
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def Frame (context d : Data) : Prop :=
  ∀ i : Fin 128, i ≠ 0 → i ≠ 1 → i ≠ 14 → i ≠ 110 → i ≠ 111 →
    d.stacks i = context.stacks i

structure Invariant (context d : Data) : Prop where
  frame : Frame context d
  xEmpty : d.stacks 0 = []
  sourceEmpty : d.stacks 1 = []

def outputStep (source : List Bool → List Bool) (D width : ℕ)
    (bits out : List Bool) : List Bool :=
  UnaryGridProgram.gridOutput (SubexpExtractionGrid.step bits (source bits) width) D D out

def SourceSpec (service : Code) (valid : List Bool → Prop)
    (source : List Bool → List Bool) (T W : ℕ) (context : Data) : Prop :=
  ∀ bits d, valid bits → Frame context d → d.stacks 0 = bits → d.stacks 1 = [] →
    ∃ n e, n ≤ T ∧ (source bits).length ≤ W ∧ Eval service n d e ∧
      e.stacks = Function.update d.stacks 1 (source bits)

def moveX : Code := .call (StackRoutines.transferProgram 111 0 0 1)

def movedX (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 111 0 d.stacks⟩

theorem moveX_eval (d : Data) :
    Eval moveX (3 * (d.stacks 111).length + 3) d (movedX d) := by
  apply Eval.call
  exact ListRegisterProgram.transfer_run 111 0 0 1 (by decide) (by decide) d.regs d.stacks

def clear (i : Fin 128) : Code := .call (StackRoutines.clearProgram i 0 1)

def cleared (i : Fin 128) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks i []⟩

theorem clear_eval (i : Fin 128) (d : Data) :
    Eval (clear i) (2 * (d.stacks i).length + 3) d (cleared i d) := by
  apply Eval.call
  exact ListRegisterProgram.clear_run i 0 1 d.regs d.stacks

def reset : Code := .base (.seq (.atom (.set 13 false))
  (.seq (.atom (.set 14 true)) (.atom (.set 15 false))))

def resetState (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 13 false) 14 true) 15 false,
    d.stacks⟩

theorem reset_eval (d : Data) : Eval reset 3 d (resetState d) := by
  have h := (StructuredProgram.Eval.atom (.set (13 : Fin 16) false) d).seq
    ((StructuredProgram.Eval.atom (.set (14 : Fin 16) true) _).seq
      (StructuredProgram.Eval.atom (.set (15 : Fin 16) false) _))
  exact .base (by simpa [resetState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h)

def callback (service : Code) : Code := .seq moveX (.seq service
  (.seq SubexpExtractionHost.gridCall (.seq (clear 0) (.seq (clear 1) reset))))

def callbackCost (D width T W : ℕ) (bits : List Bool) : ℕ :=
  T + 5 * bits.length + D * (D + 1) *
    (100 * (bits.length + W + 2 * D + width + 2)) +
    13 * D ^ 2 + 31 * D + 21 * W + 44

def work : List (Fin 128) := [4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 17]

structure Context (context : Data) (D width : ℕ) : Prop where
  dimension : context.stacks 2 = List.replicate D true
  width : context.stacks 3 = List.replicate width true
  clean : ∀ i ∈ work, context.stacks i = []

theorem callback_contract (service : Code) (valid : List Bool → Prop)
    (source : List Bool → List Bool) (D width T W : ℕ) (context : Data)
    (hc : Context context D width) (spec : SourceSpec service valid source T W context) :
    RecordPrograms.CallbackContractWithOn ports (callback service) (fun _ => false)
      (callbackCost D width T W) (Invariant context)
      (fun bits a b => b.stacks 14 = outputStep source D width bits (a.stacks 14)) valid := by
  intro bits tail base hv hi
  let a := RecordPrograms.state ports base false true false tail bits.reverse
  let b := movedX a
  have ha : Frame context a := by
    intro i h0 h1 h14 h110 h111
    simpa [a, RecordPrograms.state, ports, h110, h111] using hi.frame i h0 h1 h14 h110 h111
  have hb : Frame context b := by
    intro i h0 h1 h14 h110 h111
    simpa [b, movedX, StackRoutines.transferStacks, h0, h111] using
      ha i h0 h1 h14 h110 h111
  have hb0 : b.stacks 0 = bits := by
    simp [b, a, movedX, StackRoutines.transferStacks, RecordPrograms.state, ports, hi.xEmpty]
  have hb1 : b.stacks 1 = [] := by
    simp [b, a, movedX, StackRoutines.transferStacks, RecordPrograms.state, ports, hi.sourceEmpty]
  have hb14 : b.stacks 14 = base.stacks 14 := by
    simp [b, a, movedX, StackRoutines.transferStacks, RecordPrograms.state, ports]
  have hb110 : b.stacks 110 = tail := by
    simp [b, a, movedX, StackRoutines.transferStacks, RecordPrograms.state, ports]
  have hb111 : b.stacks 111 = [] := by simp [b, movedX, StackRoutines.transferStacks]
  obtain ⟨sn, c, hsn, hsourceLength, hs, hsc⟩ := spec bits b hv hb hb0 hb1
  have hcf : Frame context c := by
    intro i h0 h1 h14 h110 h111
    simpa [hsc, h1] using hb i h0 h1 h14 h110 h111
  have hinput : SubexpExtractionGrid.Input (SubexpExtractionHost.restrict c)
      bits (source bits) D width := by
    constructor
    · simpa [SubexpExtractionHost.restrict, SubexpExtractionHost.stackPorts, hsc] using hb0
    · simp [SubexpExtractionHost.restrict, SubexpExtractionHost.stackPorts, hsc]
    · exact (hcf 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.dimension
    · exact (hcf 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc.width
    · intro i hmem
      have hiw : SubexpExtractionHost.stackPorts i ∈ work := by
        simp only [SubexpExtractionGrid.work, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          decide
      have hne : SubexpExtractionHost.stackPorts i ≠ 0 ∧ SubexpExtractionHost.stackPorts i ≠ 1 ∧
          SubexpExtractionHost.stackPorts i ≠ 14 ∧ SubexpExtractionHost.stackPorts i ≠ 110 ∧
          SubexpExtractionHost.stackPorts i ≠ 111 := by
        simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hiw
        rcases hiw with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
      exact (hcf _ hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2).trans (hc.clean _ hiw)
  obtain ⟨gn, g, hgn, hg, hgs, _⟩ :=
    SubexpExtractionHost.gridCall_eval c bits (source bits) D width hinput
  have hc14 : c.stacks 14 = base.stacks 14 := by simpa [hsc] using hb14
  have hg0 : g.stacks 0 = bits := by simpa [hgs, hsc] using hb0
  have hg1 : g.stacks 1 = source bits := by simp [hgs, hsc]
  let f := cleared 1 (cleared 0 g)
  let e := resetState f
  have heFrame : Frame context e := by
    intro i h0 h1 h14 h110 h111
    simpa [e, f, resetState, cleared, hgs, h0, h1, h14] using
      hcf i h0 h1 h14 h110 h111
  have he0 : e.stacks 0 = [] := by simp [e, f, resetState, cleared]
  have he1 : e.stacks 1 = [] := by simp [e, f, resetState, cleared]
  have he110 : e.stacks 110 = tail := by
    simpa [e, f, resetState, cleared, hgs, hsc] using hb110
  have he111 : e.stacks 111 = [] := by
    simpa [e, f, resetState, cleared, hgs, hsc] using hb111
  have heState : RecordPrograms.state ports e false true false tail [] = e := by
    apply RecordPrograms.state_eq_self
    · simp [e, resetState, ports]
    · simp [e, resetState, ports]
    · simp [e, resetState, ports]
    · exact he110
    · exact he111
  have hrun := (moveX_eval a).seq (hs.seq (hg.seq
    ((clear_eval 0 g).seq ((clear_eval 1 (cleared 0 g)).seq (reset_eval f)))))
  refine ⟨3 * (a.stacks 111).length + 3 +
    (sn + (gn + ((2 * (g.stacks 0).length + 3) +
      ((2 * ((cleared 0 g).stacks 1).length + 3) + 3)))),
    e, ?_, ⟨heFrame, he0, he1⟩, ?_, ?_⟩
  · have hgrid : SubexpExtractionGrid.gridCost bits (source bits) D width ≤
        D * (D + 1) * (100 * (bits.length + W + 2 * D + width + 2)) +
          13 * D ^ 2 + 31 * D + 10 := by
      apply Nat.add_le_add_right
      apply Nat.add_le_add_right
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul_left _ (by omega)
    have ha111 : (a.stacks 111).length = bits.length := by
      simp [a, RecordPrograms.state, ports]
    have hclear1 : (cleared 0 g).stacks 1 = source bits := by simp [cleared, hg1]
    change 3 * (a.stacks 111).length + 3 +
      (sn + (gn + ((2 * (g.stacks 0).length + 3) +
        ((2 * ((cleared 0 g).stacks 1).length + 3) + 3)))) ≤ _
    rw [ha111, hg0, hclear1]
    dsimp [callbackCost]
    omega
  · simp [e, f, resetState, cleared, hgs, hc14, outputStep]
  · rw [heState]
    exact hrun

def command (service : Code) : Code := RecordPrograms.iterate ports (callback service)
def program (service : Code) := StructuredCalls.compiled (command service) 110 14

def allJobs (source : List Bool → List Bool) (D width : ℕ)
    (records : List (List Bool)) : List SubexpMomentProgram.Job :=
  records.flatMap fun bits => SubexpExtractionGrid.gridJobs bits (source bits) D width D

theorem fold_jobs (source : List Bool → List Bool) (D width : ℕ)
    (records : List (List Bool)) (old : List SubexpMomentProgram.Job) :
    records.foldl (fun out bits => outputStep source D width bits out) (SubexpMomentProgram.input old) =
      SubexpMomentProgram.input ((allJobs source D width records).reverse ++ old) := by
  induction records generalizing old with
  | nil => simp [allJobs]
  | cons bits rest ih =>
    rw [List.foldl_cons, outputStep, SubexpExtractionGrid.gridOutput_jobs, ih]
    simp [allJobs, List.reverse_append, List.append_assoc]

theorem allJobs_length (source : List Bool → List Bool) (D width : ℕ)
    (records : List (List Bool)) :
    (allJobs source D width records).length = records.length * (D * (D + 1)) := by
  simp [allJobs, List.length_flatMap, SubexpExtractionGrid.gridJobs_length]

/-- The theorem consumes the actual source subroutine's trace contract.
It does not populate that contract with a prepared template independent of
the current exponent. -/
theorem command_eval (service : Code) (valid : List Bool → Prop)
    (source : List Bool → List Bool) (D width T W : ℕ) (context : Data)
    (hc : Context context D width) (spec : SourceSpec service valid source T W context)
    (records : List (List Bool)) (hrecords : ∀ bits ∈ records, valid bits)
    (base : Data) (hi : Invariant context base) (old : List SubexpMomentProgram.Job)
    (hout : base.stacks 14 = SubexpMomentProgram.input old) :
    ∃ n e, n ≤ 3 + RecordPrograms.budget (callbackCost D width T W) records ∧
      Eval (command service) n
        (RecordPrograms.state ports base false false false (Encoding.encodeList id records) [])
        (RecordPrograms.state ports e false true false [] []) ∧
      Invariant context e ∧
      e.stacks 14 = SubexpMomentProgram.input ((allJobs source D width records).reverse ++ old) := by
  obtain ⟨n, e, hn, he, hv, hr⟩ := RecordPrograms.iterate_run_with_on ports (callback service)
    (fun _ => false) (callbackCost D width T W) (Invariant context)
    (fun bits a b => b.stacks 14 = outputStep source D width bits (a.stacks 14)) valid
    (callback_contract service valid source D width T W context hc spec)
    records [] base hrecords hi false false false
  have hfold := hv.fold_of_false (by intros; rfl) (fun d => d.stacks 14)
    (fun out bits => outputStep source D width bits out) (by intros; assumption)
  rw [hout, fold_jobs] at hfold
  have hany : records.any (fun _ => false) = false := by
    induction records <;> simp_all
  refine ⟨n, e, hn, ?_, he, hfold⟩
  simpa [command, hany, SubexpNormalizeProgram.unread_false] using hr

theorem program_runs (service : Code) (valid : List Bool → Prop)
    (source : List Bool → List Bool) (D width T W : ℕ) (context : Data)
    (hc : Context context D width) (spec : SourceSpec service valid source T W context)
    (records : List (List Bool)) (hrecords : ∀ bits ∈ records, valid bits)
    (base : Data) (hi : Invariant context base) (old : List SubexpMomentProgram.Job)
    (hout : base.stacks 14 = SubexpMomentProgram.input old) :
    ∃ e : Data, RunsIn (program service)
      (4 + RecordPrograms.budget (callbackCost D width T W) records)
      ((RecordPrograms.state ports base false false false (Encoding.encodeList id records) []).withPC
        (some (program service).entry))
      ((RecordPrograms.state ports e false true false [] []).withPC none) ∧
      Invariant context e ∧
      e.stacks 14 = SubexpMomentProgram.input ((allJobs source D width records).reverse ++ old) := by
  obtain ⟨n, e, hn, he, hi', hout'⟩ :=
    command_eval service valid source D width T W context hc spec records hrecords base hi old hout
  exact ⟨e, ⟨n + 1, by omega, StructuredCalls.compiled_halt_trace he 110 14⟩, hi', hout'⟩

theorem program_primitive (service : Code) (valid : List Bool → Prop)
    (source : List Bool → List Bool) (D width T W : ℕ) (context : Data)
    (hc : Context context D width) (spec : SourceSpec service valid source T W context)
    (records : List (List Bool)) (hrecords : ∀ bits ∈ records, valid bits)
    (base : Data) (hi : Invariant context base) (old : List SubexpMomentProgram.Job)
    (hout : base.stacks 14 = SubexpMomentProgram.input old) :
    ∃ e : Data, Computation.RunsIn (BitProgram.primitive (program service)).step
      (BitProgram.primitiveOverhead (program service) *
        (4 + RecordPrograms.budget (callbackCost D width T W) records))
      (BitProgram.primitiveCfg (program service)
        ((RecordPrograms.state ports base false false false (Encoding.encodeList id records) []).withPC
          (some (program service).entry)))
      (BitProgram.primitiveCfg (program service)
        ((RecordPrograms.state ports e false true false [] []).withPC none)) ∧
      e.stacks 14 = SubexpMomentProgram.input ((allJobs source D width records).reverse ++ old) := by
  obtain ⟨e, he, _, hout'⟩ :=
    program_runs service valid source D width T W context hc spec records hrecords base hi old hout
  exact ⟨e, BitProgram.primitive_execution _ he, hout'⟩

def momentRecords (D : ℕ) : List (List Bool) :=
  ((Algorithm.exponentList D (2 * D + 1)).reverse).map SubexpExponentController.momentWord

def ValidMoment (D : ℕ) (bits : List Bool) : Prop :=
  ∃ a : Fin D → ℕ, a ∈ Algorithm.exponentList D (2 * D + 1) ∧
    bits = SubexpExponentController.momentWord a

theorem momentRecords_valid (D : ℕ) (bits : List Bool) (h : bits ∈ momentRecords D) :
    ValidMoment D bits := by
  rcases List.mem_map.mp h with ⟨a, ha, rfl⟩
  exact ⟨a, List.mem_reverse.mp ha, rfl⟩

theorem momentRecords_length (D : ℕ) :
    (momentRecords D).length = (3 * D + 1).choose D := by
  simp only [momentRecords, List.length_map, List.length_reverse, Algorithm.exponentList_length]
  congr 1
  omega

theorem momentJobs_length (source : List Bool → List Bool) (D width : ℕ) :
    (allJobs source D width (momentRecords D)).length =
      (3 * D + 1).choose D * (D * (D + 1)) := by
  rw [allJobs_length, momentRecords_length]

theorem allJobs_generated {D : ℕ} {C : Type*}
    (source : List Bool → List Bool) (encode : SymbolicCost.CoeffList D C → List Bool)
    (expression : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D C))
    (hsource : ∀ a ∈ Algorithm.exponentList D (2 * D + 1),
      source (SubexpExponentController.momentWord a) =
        SubexpPostfixControl.serializeCode encode (expression a).compile) :
    (allJobs source D (SubexpSymbolicCost.indexBits D) (momentRecords D)).reverse =
      SubexpQueryOrder.generatedJobs encode expression := by
  unfold allJobs momentRecords SubexpQueryOrder.generatedJobs SubexpQueryOrder.generatedQueries
  conv_rhs => rw [List.map_reverse]
  apply congrArg List.reverse
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro a ha
  have hamem := List.mem_reverse.mp ha
  have habound := (Algorithm.mem_exponentList D (2 * D + 1) a).mp hamem
  change SubexpExtractionGrid.gridJobs (SymbolicCost.unaryWords (List.ofFn a))
    (source (SubexpExponentController.momentWord a)) D (SubexpSymbolicCost.indexBits D) D = _
  rw [SubexpExtractionGrid.gridJobs_eq_fixedKey a _ habound, hsource a hamem]
  simp [SubexpQueryOrder.perMoment, List.map_flatMap, List.map_map, Function.comp_def]

/-- Specialization to the exact record order emitted by the independently
checked degree-budget exponent controller. -/
theorem moments_program_runs (service : Code) (source : List Bool → List Bool)
    (D width T W : ℕ) (context : Data) (hc : Context context D width)
    (spec : SourceSpec service (ValidMoment D) source T W context)
    (base : Data) (hi : Invariant context base) (old : List SubexpMomentProgram.Job)
    (hout : base.stacks 14 = SubexpMomentProgram.input old) :
    ∃ e : Data, RunsIn (program service)
      (4 + RecordPrograms.budget (callbackCost D width T W) (momentRecords D))
      ((RecordPrograms.state ports base false false false
        (Encoding.encodeList id (momentRecords D)) []).withPC (some (program service).entry))
      ((RecordPrograms.state ports e false true false [] []).withPC none) ∧
      Invariant context e ∧
      e.stacks 14 = SubexpMomentProgram.input
        ((allJobs source D width (momentRecords D)).reverse ++ old) :=
  program_runs service (ValidMoment D) source D width T W context hc spec
    (momentRecords D) (momentRecords_valid D) base hi old hout

end SubexponentialSAT.SubexpOuterJobs

end OAI.Algorithms
