import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOuterJobs
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Relocating the actual outer job loop into the node workspace

The local job workspace occupies 138 through 255. Its ten external source
ports use a fixed subset of the low ports. The adapter initializes the real
output delimiter and iterator flags, calls the actual outer loop, and moves
its forward output to port 100 using two measured stack transfers.

The per-exponent source-service contract remains an explicit premise. This
module does not replace that service by a semantic source oracle.
-/

namespace SubexponentialSAT.SubexpNodeJobsStage

open BitProgram StructuredCalls

abbrev Data := State 16 256
abbrev Code := Cmd 16 256
abbrev Local := SubexpOuterJobs.Data

def sourcePort : Fin 10 → Fin 256 := ![0, 1, 2, 3, 4, 6, 7, 8, 9, 11]

theorem sourcePort_injective : Function.Injective sourcePort := by decide

theorem sourcePort_le (i : Fin 10) : (sourcePort i).val ≤ 11 := by
  fin_cases i <;> decide

def port (i : Fin 128) : Fin 256 :=
  if h : i.val < 118 then ⟨138 + i.val, by omega⟩
  else sourcePort ⟨i.val - 118, by omega⟩

theorem port_injective : Function.Injective port := by
  intro i j he
  by_cases hi : i.val < 118
  · by_cases hj : j.val < 118
    · apply Fin.ext
      have hv := congrArg Fin.val he
      simp only [port, dite_eq_left hi, dite_eq_left hj] at hv
      omega
    · have hv := congrArg Fin.val he
      simp only [port, dite_eq_left hi, dite_eq_right hj] at hv
      have hb := sourcePort_le ⟨j.val - 118, by omega⟩
      omega
  · by_cases hj : j.val < 118
    · have hv := congrArg Fin.val he
      simp only [port, dite_eq_right hi, dite_eq_left hj] at hv
      have hb := sourcePort_le ⟨i.val - 118, by omega⟩
      omega
    · simp only [port, dite_eq_right hi, dite_eq_right hj] at he
      have hv := congrArg Fin.val (sourcePort_injective he)
      apply Fin.ext
      dsimp only at hv
      omega

@[simp] theorem port_zero : port 0 = 138 := rfl
@[simp] theorem port_one : port 1 = 139 := rfl
@[simp] theorem port_output : port 14 = 152 := rfl
@[simp] theorem port_input : port 110 = 248 := rfl
@[simp] theorem port_payload : port 111 = 249 := rfl
@[simp] theorem port_master : port 117 = 255 := rfl

def project (d : Data) : Local := projectState id port d

def jobs (service : SubexpOuterJobs.Code) : Code :=
  .call (ProgramLinking.liftProgram (SubexpOuterJobs.program service) id port)

def output (source : List Bool → List Bool) (D width : ℕ) : List Bool :=
  SubexpMomentProgram.input
    (SubexpOuterJobs.allJobs source D width (SubexpOuterJobs.momentRecords D)).reverse

theorem output_generated {D : ℕ} {C : Type*}
    (source : List Bool → List Bool) (encode : SymbolicCost.CoeffList D C → List Bool)
    (expression : (Fin D → ℕ) → Algorithm.Expr (SymbolicCost.CoeffList D C))
    (hsource : ∀ a ∈ Algorithm.exponentList D (2 * D + 1),
      source (SubexpExponentController.momentWord a) =
        SubexpPostfixControl.serializeCode encode (expression a).compile) :
    output source D (SubexpSymbolicCost.indexBits D) =
      SubexpMomentProgram.input (SubexpQueryOrder.generatedJobs encode expression) := by
  unfold output
  rw [SubexpOuterJobs.allJobs_generated source encode expression hsource]

def loopBound (D width T W : ℕ) : ℕ :=
  4 + RecordPrograms.budget (SubexpOuterJobs.callbackCost D width T W)
    (SubexpOuterJobs.momentRecords D)

/-- A relocated call with its exact stack update. The unused local port 117
is covered by the source service's frame, so physical master 255 survives. -/
theorem jobs_eval (service : SubexpOuterJobs.Code) (source : List Bool → List Bool)
    (D width T W : ℕ) (context : Local)
    (hc : SubexpOuterJobs.Context context D width)
    (spec : SubexpOuterJobs.SourceSpec service (SubexpOuterJobs.ValidMoment D) source T W context)
    (d : Data) (hf : SubexpOuterJobs.Frame context (project d))
    (h138 : d.stacks 138 = []) (h139 : d.stacks 139 = [])
    (h152 : d.stacks 152 = [false])
    (h248 : d.stacks 248 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (h249 : d.stacks 249 = [])
    (h13 : d.regs 13 = false) (h14 : d.regs 14 = false) (h15 : d.regs 15 = false) :
    ∃ n e, n ≤ loopBound D width T W ∧ Eval (jobs service) n d e ∧
      e.stacks = Function.update (Function.update d.stacks 248 []) 152 (output source D width) := by
  have hi : SubexpOuterJobs.Invariant context (project d) := ⟨hf, h138, h139⟩
  obtain ⟨e, ⟨n, hn, ht⟩, hei, heout⟩ :=
    SubexpOuterJobs.moments_program_runs service source D width T W context hc spec
      (project d) hi [] h152
  have hstart : RecordPrograms.state SubexpOuterJobs.ports (project d) false false false
      (Encoding.encodeList id (SubexpOuterJobs.momentRecords D)) [] = project d := by
    apply RecordPrograms.state_eq_self
    · exact h13
    · exact h14
    · exact h15
    · exact h248
    · exact h249
  rw [hstart] at ht
  let f := RecordPrograms.state SubexpOuterJobs.ports e false true false [] []
  let result := embedState id port d f
  refine ⟨n, result, hn, eval_call_from_state _ _ _ _ Function.injective_id port_injective ht, ?_⟩
  funext i
  by_cases hi : ∃ j, port j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [show result.stacks (port j) = f.stacks j from
      embedState_stack id port d f port_injective j]
    have hports : port j = 248 ↔ j = 110 := by
      change port j = port 110 ↔ j = 110
      exact port_injective.eq_iff
    have hout : port j = 152 ↔ j = 14 := by
      change port j = port 14 ↔ j = 14
      exact port_injective.eq_iff
    by_cases h110 : j = 110
    · subst j
      simp [f, RecordPrograms.state, SubexpOuterJobs.ports]
    by_cases h111 : j = 111
    · subst j
      simp [f, RecordPrograms.state, SubexpOuterJobs.ports, port_payload, h249]
    by_cases h0 : j = 0
    · subst j
      simpa [f, RecordPrograms.state, SubexpOuterJobs.ports, h138] using hei.xEmpty
    by_cases h1 : j = 1
    · subst j
      simpa [f, RecordPrograms.state, SubexpOuterJobs.ports, h139] using hei.sourceEmpty
    by_cases h14' : j = 14
    · subst j
      simpa [f, RecordPrograms.state, SubexpOuterJobs.ports, output] using heout
    · have heq := (hei.frame j h0 h1 h14' h110 h111).trans
        (hf j h0 h1 h14' h110 h111).symm
      simpa [f, RecordPrograms.state, SubexpOuterJobs.ports, h110, h111,
        Function.update_apply, hports, hout, h14', project, projectState] using heq
  · rw [show result.stacks i = d.stacks i from
      embedState_stack_frame id port d f i hi]
    have h248 : i ≠ 248 := fun h => hi ⟨110, by simpa using h.symm⟩
    have h152 : i ≠ 152 := fun h => hi ⟨14, by simpa using h.symm⟩
    simp [h248, h152]

def initializeOutput : Code := .base (.seq (.atom (.set 13 false))
  (.seq (.atom (.set 14 false)) (.seq (.atom (.set 15 false)) (.atom (.push 152 13)))))

def initialized (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 13 false) 14 false) 15 false,
    Function.update d.stacks 152 (false :: d.stacks 152)⟩

theorem initializeOutput_eval (d : Data) : Eval initializeOutput 4 d (initialized d) := by
  have h := (StructuredProgram.Eval.atom (.set (13 : Fin 16) false) d).seq
    ((StructuredProgram.Eval.atom (.set (14 : Fin 16) false) _).seq
      ((StructuredProgram.Eval.atom (.set (15 : Fin 16) false) _).seq
        (StructuredProgram.Eval.atom (.push (152 : Fin 256) (13 : Fin 16)) _)))
  exact .base (by simpa [initialized, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h)

def transfer (src dst : Fin 256) : Code :=
  .call (StackRoutines.transferProgram src dst 0 1)

def transferred (src dst : Fin 256) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 256) (hsd : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred src dst d) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide) d.regs d.stacks)

def moveOutput : Code := .seq (transfer 152 139) (transfer 139 100)
def moved (d : Data) : Data := transferred 139 100 (transferred 152 139 d)

theorem moveOutput_eval (d : Data) (h139 : d.stacks 139 = []) :
    Eval moveOutput (6 * (d.stacks 152).length + 6) d (moved d) := by
  have h := (transfer_eval 152 139 (by decide) d).seq
    (transfer_eval 139 100 (by decide) (transferred 152 139 d))
  convert h using 1
  all_goals simp [moveOutput, moved, transferred, StackRoutines.transferStacks, h139]
  all_goals omega

theorem moved_stacks (d : Data) (h139 : d.stacks 139 = []) (h100 : d.stacks 100 = []) :
    (moved d).stacks = Function.update (Function.update d.stacks 152 []) 100 (d.stacks 152) := by
  funext i
  by_cases hi152 : i = 152
  · subst i; simp [moved, transferred, StackRoutines.transferStacks]
  by_cases hi139 : i = 139
  · subst i; simp [moved, transferred, StackRoutines.transferStacks, h139]
  by_cases hi100 : i = 100
  · subst i; simp [moved, transferred, StackRoutines.transferStacks, h139, h100]
  · simp [moved, transferred, StackRoutines.transferStacks, hi152, hi139, hi100]

def command (service : SubexpOuterJobs.Code) : Code :=
  .seq initializeOutput (.seq (jobs service) moveOutput)
def program (service : SubexpOuterJobs.Code) := compiled (command service) 248 100

def bound (source : List Bool → List Bool) (D width T W : ℕ) : ℕ :=
  11 + loopBound D width T W + 6 * (output source D width).length

/-- This is a measured invocation of the actual outer program. The only
remaining source obligation is exactly its explicit SourceSpec premise. -/
theorem command_eval_in_context (service : SubexpOuterJobs.Code) (source : List Bool → List Bool)
    (D width T W : ℕ) (context : Local) (d : Data)
    (hc : SubexpOuterJobs.Context context D width)
    (spec : SubexpOuterJobs.SourceSpec service (SubexpOuterJobs.ValidMoment D) source T W context)
    (hframe : SubexpOuterJobs.Frame context (project d))
    (h138 : d.stacks 138 = []) (h139 : d.stacks 139 = [])
    (h152 : d.stacks 152 = []) (h100 : d.stacks 100 = [])
    (h248 : d.stacks 248 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (h249 : d.stacks 249 = []) :
    ∃ n e, n + 1 ≤ bound source D width T W ∧ Eval (command service) n d e ∧
      e.stacks = Function.update (Function.update d.stacks 248 []) 100 (output source D width) := by
  let a := initialized d
  have hf : SubexpOuterJobs.Frame context (project a) := by
    intro i h0 h1 h14 h110 h111
    have hp : port i ≠ 152 := by
      change port i ≠ port 14
      exact port_injective.ne h14
    simpa [a, initialized, project, projectState, hp] using hframe i h0 h1 h14 h110 h111
  obtain ⟨n, e, hn, he, hs⟩ := jobs_eval service source D width T W context hc spec a hf
    (by simp [a, initialized, h138]) (by simp [a, initialized, h139])
    (by simp [a, initialized, h152]) (by simp [a, initialized, h248])
    (by simp [a, initialized, h249])
    (by simp [a, initialized]) (by simp [a, initialized]) (by simp [a, initialized])
  have he139 : e.stacks 139 = [] := by simp [hs, a, initialized, h139]
  have he100 : e.stacks 100 = [] := by simp [hs, a, initialized, h100]
  have he152 : e.stacks 152 = output source D width := by simp [hs]
  refine ⟨4 + (n + (6 * (e.stacks 152).length + 6)), moved e, ?_,
    (initializeOutput_eval d).seq (he.seq (moveOutput_eval e he139)), ?_⟩
  · rw [he152]
    unfold bound
    omega
  · rw [moved_stacks e he139 he100, hs]
    funext i
    by_cases hi100 : i = 100
    · subst i; simp
    by_cases hi152 : i = 152
    · subst i; simp [a, initialized, h152]
    by_cases hi248 : i = 248
    · subst i; simp [hi100]
    · simp [a, initialized, hi100, hi152, hi248]

theorem command_eval (service : SubexpOuterJobs.Code) (source : List Bool → List Bool)
    (D width T W : ℕ) (d : Data)
    (hc : SubexpOuterJobs.Context (project d) D width)
    (spec : SubexpOuterJobs.SourceSpec service (SubexpOuterJobs.ValidMoment D) source T W (project d))
    (h138 : d.stacks 138 = []) (h139 : d.stacks 139 = [])
    (h152 : d.stacks 152 = []) (h100 : d.stacks 100 = [])
    (h248 : d.stacks 248 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (h249 : d.stacks 249 = []) :
    ∃ n e, n + 1 ≤ bound source D width T W ∧ Eval (command service) n d e ∧
      e.stacks = Function.update (Function.update d.stacks 248 []) 100 (output source D width) :=
  command_eval_in_context service source D width T W (project d) d hc spec
    (fun _ _ _ _ _ _ => rfl) h138 h139 h152 h100 h248 h249

theorem program_runs (service : SubexpOuterJobs.Code) (source : List Bool → List Bool)
    (D width T W : ℕ) (d : Data)
    (hc : SubexpOuterJobs.Context (project d) D width)
    (spec : SubexpOuterJobs.SourceSpec service (SubexpOuterJobs.ValidMoment D) source T W (project d))
    (h138 : d.stacks 138 = []) (h139 : d.stacks 139 = [])
    (h152 : d.stacks 152 = []) (h100 : d.stacks 100 = [])
    (h248 : d.stacks 248 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (h249 : d.stacks 249 = []) :
    ∃ e : Data, RunsIn (program service) (bound source D width T W)
      (d.withPC (some (program service).entry)) (e.withPC none) ∧
      e.stacks = Function.update (Function.update d.stacks 248 []) 100 (output source D width) := by
  obtain ⟨n, e, hn, he, hs⟩ := command_eval service source D width T W d hc spec
    h138 h139 h152 h100 h248 h249
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 248 100⟩, hs⟩

def copyMomentMaster : Code := SubexpSetupStorage.copyCmd 127 248 139
def fromMaster (service : SubexpOuterJobs.Code) : Code :=
  .seq copyMomentMaster (command service)
def masterProgram (service : SubexpOuterJobs.Code) := compiled (fromMaster service) 127 100

def masterBound (source : List Bool → List Bool) (D width T W : ℕ) (d : Data) : ℕ :=
  7 * (d.stacks 127).length + 5 + bound source D width T W

/-- Reuse the retained exponent stream on 127 for each node. Both the master
stream and the dense-row master 255 survive, and all job scratch is restored. -/
theorem master_program_runs (service : SubexpOuterJobs.Code) (source : List Bool → List Bool)
    (D width T W : ℕ) (d : Data)
    (hc : SubexpOuterJobs.Context (project d) D width)
    (spec : SubexpOuterJobs.SourceSpec service (SubexpOuterJobs.ValidMoment D) source T W (project d))
    (h138 : d.stacks 138 = []) (h139 : d.stacks 139 = [])
    (h152 : d.stacks 152 = []) (h100 : d.stacks 100 = [])
    (h127 : d.stacks 127 = Encoding.encodeList id (SubexpOuterJobs.momentRecords D))
    (h248 : d.stacks 248 = []) (h249 : d.stacks 249 = []) :
    ∃ e : Data, RunsIn (masterProgram service) (masterBound source D width T W d)
      (d.withPC (some (masterProgram service).entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 100 (output source D width) := by
  let a := SubexpSetupStorage.copyState 127 248 d
  have hcopy : Eval copyMomentMaster (7 * (d.stacks 127).length + 5) d a :=
    SubexpSetupStorage.copy_eval 127 248 139 d (by decide) (by decide) (by decide) h139
  have hf : SubexpOuterJobs.Frame (project d) (project a) := by
    intro i h0 h1 h14 h110 h111
    have hp : port i ≠ 248 := by
      change port i ≠ port 110
      exact port_injective.ne h110
    simp [a, SubexpSetupStorage.copyState_stack, project, projectState, hp]
  obtain ⟨n, e, hn, he, hs⟩ := command_eval_in_context service source D width T W
    (project d) a hc spec hf
    (by simp [a, SubexpSetupStorage.copyState_stack, h138])
    (by simp [a, SubexpSetupStorage.copyState_stack, h139])
    (by simp [a, SubexpSetupStorage.copyState_stack, h152])
    (by simp [a, SubexpSetupStorage.copyState_stack, h100])
    (by simp [a, SubexpSetupStorage.copyState_stack, h127, h248])
    (by simp [a, SubexpSetupStorage.copyState_stack, h249])
  refine ⟨e, ⟨(7 * (d.stacks 127).length + 5 + n) + 1, ?_,
    compiled_halt_trace (hcopy.seq he) 127 100⟩, ?_⟩
  · unfold masterBound
    omega
  · rw [hs]
    funext i
    by_cases hi100 : i = 100
    · subst i; simp
    by_cases hi248 : i = 248
    · subst i; simp [h248]
    · simp [a, SubexpSetupStorage.copyState_stack, hi100, hi248]

/-- All persistent tables survive, including source ports 128 through 137
and the dense-row master on 255. -/
theorem result_frame (d e : Data) (bits : List Bool)
    (he : e.stacks = Function.update (Function.update d.stacks 248 []) 100 bits)
    (i : Fin 256) (h248 : i ≠ 248) (h100 : i ≠ 100) : e.stacks i = d.stacks i := by
  simp [he, h248, h100]

theorem result_protected (d e : Data) (bits : List Bool)
    (he : e.stacks = Function.update (Function.update d.stacks 248 []) 100 bits) :
    e.stacks 5 = d.stacks 5 ∧ e.stacks 10 = d.stacks 10 ∧
      e.stacks 25 = d.stacks 25 ∧ e.stacks 91 = d.stacks 91 ∧
      e.stacks 92 = d.stacks 92 ∧ e.stacks 255 = d.stacks 255 ∧
      (∀ i : Fin 256, 128 ≤ i.val → i.val < 138 → e.stacks i = d.stacks i) := by
  refine ⟨result_frame d e bits he 5 (by decide) (by decide),
    result_frame d e bits he 10 (by decide) (by decide),
    result_frame d e bits he 25 (by decide) (by decide),
    result_frame d e bits he 91 (by decide) (by decide),
    result_frame d e bits he 92 (by decide) (by decide),
    result_frame d e bits he 255 (by decide) (by decide), ?_⟩
  intro i hlo hhi
  apply result_frame d e bits he i
  · intro h; have hv := congrArg Fin.val h; change i.val = 248 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change i.val = 100 at hv; omega

end SubexponentialSAT.SubexpNodeJobsStage

end OAI.Algorithms
