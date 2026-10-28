import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramPorts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramWords
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramBoot
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramScalar
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgramPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramConstantsModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramNative
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramReady

namespace OAI.Algorithms


/- Component: LeafRingSetupProgramScalar.lean -/

/-! The first concrete stage of ring setup.  Only the runtime binary
precision is supplied.  The generated scalar cache remains exposed while
the extension-ring table and constants are built.  The idempotent producer
later uses a separately framed preparation, with its own charged cost. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpQuarticRing
open IdempotentPreparationProgram

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev scalarCommand : Cmd 8 41 := .seq boot Scalar.command

def scalarBudget (t inputWidth : ℕ) : ℕ :=
  2001 * (t + inputWidth + 2)^2 + 500000 * (3*t + inputWidth + 1)^3

structure ScalarOutput (t : ℕ) (bits : List Bool)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) (logword : List Bool)
    (out : IdempotentPreparationProgram.Data) : Prop where
  prepared : Scalar.Prepared t M cache u out
  logValue : CounterPrograms.value logword = Nat.clog 2 t
  logLength : logword.length ≤ bits.length + 1
  unchanged : ∀ j, (∀ i, Scalar.port i ≠ j) →
    out.stacks j = bootStacks t bits M.bits logword j

/-- This is an actual instruction trace from the one-word input, not an
assumption that a scalar cache or a modulus was supplied. -/
theorem scalarCommand_eval (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits = t) (ht : 0 < t) :
    ∃ n out, ∃ (M : SubexpPreparedQuartic.Modulus 3 t)
      (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t), ∃ logword,
      Eval scalarCommand n (inputData bits) out ∧
      ScalarOutput t bits M cache u logword out ∧ n ≤ scalarBudget t bits.length := by
  obtain ⟨M, logword, nb, rb, hlog, hlen, hnb, heb⟩ := boot_eval bits t hv ht
  let a : IdempotentPreparationProgram.Data := ⟨rb, bootStacks t bits M.bits logword⟩
  let W := 2*t + bits.length
  have hs : (List.replicate (2*t) true).length = SubexpLiftRing.baseWidth 3 t := by
    simp [RingProgram.ternary_baseWidth]
  have hr : Scalar.Rest a M.bits := by
    constructor
    · intro i; fin_cases i <;> simp [a, Scalar.low, bootStacks]
    · simp [a, bootStacks]
  have hp : ∀ i, (a.stacks (Scalar.port i)).length ≤ W := by
    intro i
    fin_cases i <;> simp [a, Scalar.port, bootStacks, W]
  obtain ⟨ns, out, cache, u, he, ho, hf, hn⟩ := Scalar.command_prepares t ht M
    (List.replicate (2*t) true) hs a W hr (by simp [a, bootStacks])
    (by simp [W]) hp (by simp [a, bootStacks]) (by simp [a, bootStacks])
  refine ⟨nb + ns, out, M, cache, u, logword, heb.seq he,
    ⟨ho, hlog, hlen, hf⟩, ?_⟩
  have hscalar := hn.trans (Scalar.budget_polynomial t W)
  rw [show t+W+1=3*t+bits.length+1 by dsimp [W]; omega] at hscalar
  unfold scalarBudget
  omega

abbrev scalarCall : Cmd 32 640 :=
  liftCommand scalarCommand 31 17 (registers 8 (by decide)) scalar

/-- The local preparation executes on the declared physical ports. The
single input word is checked against the caller projection, and all other
caller tapes are framed by the actual lifted call. -/
theorem scalarCall_eval (a : LeafRingSetupProgram.Data) (bits : List Bool) (t : ℕ)
    (hv : CounterPrograms.value bits = t) (ht : 0 < t)
    (ha : projectState (registers 8 (by decide)) scalar a = inputData bits) :
    ∃ n out, ∃ (M : SubexpPreparedQuartic.Modulus 3 t)
      (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t), ∃ logword,
      Eval scalarCall n a (embedState (registers 8 (by decide)) scalar a out) ∧
      ScalarOutput t bits M cache u logword out ∧ n ≤ scalarBudget t bits.length + 1 := by
  obtain ⟨n,out,M,cache,u,logword,he,ho,hn⟩ := scalarCommand_eval bits t hv ht
  have he' : Eval scalarCommand n (projectState (registers 8 (by decide)) scalar a) out :=
    ha.symm ▸ he
  exact ⟨n+1,out,M,cache,u,logword,
    eval_liftCommand_from_state scalarCommand 31 17 (registers 8 (by decide)) scalar a
      (registers_injective 8 (by decide)) scalar_injective he',
    ho,Nat.add_le_add_right hn 1⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram


/- Component: LeafRingSetupProgramSearch.lean -/

/-! Actual irreducible search followed by coefficient padding.  The model
below is the one selected by the finite search, not a supplied polynomial. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing


abbrev searchCall : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram IrreducibleSearchBootstrap.searchProgram
    (registers 22 (by decide)) search)

abbrev paddingCall : Cmd 32 640 :=
  liftCommand RingCoefficientLiftProgram.searchCommand 13 21
    (registers 22 (by decide)) search

/-- Only the unary degree is initially present in the local search workspace.
The caller's modulus, scalar cache and width tapes lie outside that workspace. -/
theorem searchCall_eval (a : Data) (depth : List Bool) (hd : 0 < depth.length)
    (ha : projectState (registers 22 (by decide)) search a =
      IrreducibleSearchBootstrap.input depth) :
    ∃ n ≤ IrreducibleSearchBootstrap.totalCost depth.length,
      ∃ out : StructuredProgram.State 22 28,
        Eval searchCall n a (embedState (registers 22 (by decide)) search a out) ∧
        out.stacks 13 = IrreducibleSearchProgram.coefficientArray
          (List.ofFn (IrreducibleSearch.data hd).coefficients) ∧
        IrreducibleSearchCandidateControl.Ready depth.length depth (false::depth) [] out ∧
        out.stacks 25 = [] ∧
        (out.stacks 12).length ≤ IrreducibleSearchBootstrap.totalCost depth.length := by
  obtain ⟨out,ho,hr,h25,n,hn,he⟩ :=
    IrreducibleSearchBootstrap.searchProgram_runsIn depth hd
  have hg := Subexp.SequentialProgram.trace_stack_length_le he (12 : Fin 28)
  have hw : (out.stacks 12).length ≤ n := by
    simpa [IrreducibleSearchBootstrap.input, StructuredProgram.ioState,
      StructuredProgram.State.withPC] using hg
  refine ⟨n,hn,out,?_,?_,hr,h25,hw.trans hn⟩
  · exact eval_call_from_state IrreducibleSearchBootstrap.searchProgram
      (registers 22 (by decide)) search a (registers_injective 22 (by decide))
      search_injective (ha.symm ▸ he)
  · simpa only [IrreducibleSearch.data_coefficients,
      IrreducibleSearchProgram.coefficientArray_ofFn] using ho

/-- The raw search's scratch certificate is exactly sufficient for the
padding routine once the separately generated scalar-width word is copied
onto local12.  This statement is only a state-description lemma; the copy
itself is paid by `overwrite_eval`. -/
theorem search_padding_ready (depth : List Bool)
    (raw : StructuredProgram.State 22 28)
    (hr : IrreducibleSearchCandidateControl.Ready depth.length depth (false::depth) [] raw)
    (h25 : raw.stacks 25 = []) (width : List Bool) (r : Fin 22 → Bool) :
    RingCoefficientLiftProgram.SearchReady
      (⟨r,Function.update raw.stacks 12 width⟩ : StructuredProgram.State 22 28) := by
  obtain ⟨h15,h21,h23,h26⟩ := hr.scratch
  exact ⟨by simpa using h23,by simpa using h15,by simpa using h25,
    by simpa using h26,by simpa using h21⟩

/-- Padding is executed on the actual caller workspace.  Every stack other
than source13 and output21 is preserved, including the original degree14. -/
theorem paddingCall_eval (a : Data) (t : ℕ) (ht : 0 < t)
    (d : ℕ) (hd : 0 < d)
    (hr : RingCoefficientLiftProgram.SearchReady
      (projectState (registers 22 (by decide)) search a))
    (hi : a.stacks 195 = IrreducibleSearchProgram.coefficientArray
      (List.ofFn (IrreducibleSearch.data hd).coefficients))
    (hw : (a.stacks 432).length = baseWidth 3 t) :
    ∃ out : Data, Eval paddingCall (d*(28*t+14)+7) a out ∧
      out.stacks = Function.update (Function.update a.stacks 195 []) 441
        (RingProgram.flat (RingProgram.liftCoefficientsRun t
          (IrreducibleSearch.data hd).coefficients).1) := by
  let localState := projectState (registers 22 (by decide)) search a
  obtain ⟨e,he,hs,hregs⟩ := RingCoefficientLiftProgram.searchCommand_eval t ht
    (IrreducibleSearch.data hd).coefficients localState hr
    (by simpa [localState,projectState,search] using hi)
    (by simpa [localState,projectState,search] using hw)
  refine ⟨embedState (registers 22 (by decide)) search a e,?_,?_⟩
  · simpa [paddingCall,Nat.add_assoc] using
      eval_liftCommand_from_state RingCoefficientLiftProgram.searchCommand 13 21
        (registers 22 (by decide)) search a (registers_injective 22 (by decide))
        search_injective he
  · change Function.extend search e.stacks a.stacks = _
    rw [hs,ProgramLinking.extend_update search_injective,
      ProgramLinking.extend_update search_injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project (registers 22 (by decide)) search a
        (registers_injective 22 (by decide)) search_injective)
    change Function.extend search localState.stacks a.stacks = a.stacks at hb
    rw [hb]
    rfl

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramTable.lean -/

/-! Table generation for the cache produced by the native scalar stage.
The cache is not replaced by a separately chosen mathematical cache. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open RingProgramTable

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev tableCall : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram RingProgramTable.Machine.program
    (registers 8 (by decide)) table)

theorem table_program_run (t : ℕ) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (ho : BinaryArithmetic.toNat cache.one.val < 3^t)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth 3 t) (hdegree : s.degree.length = d) :
    ∃ rf, RunsIn Machine.program (208000*(d+1)^5*(t+1)^2)
      ((Machine.state regs
        (initialStore s (modelCoefficients t a) cache.one cache.zero cache.minusOne) []).withPC
        (some Machine.program.entry))
      ((Machine.state rf (preparedStore 3 t M cache (modelCoefficients t a) s)
        (modelTable t a M cache)).withPC none) := by
  let c := modelCoefficients t a
  obtain ⟨rf, n, hn, he⟩ := Machine.program_run 3 t M cache hd c hz ho s regs
    hmod hw hdegree
  refine ⟨rf, n, ?_, ?_⟩
  · apply hn.trans
    apply (Machine.nativeBudget_polynomial (baseWidth 3 t) d).trans
    rw [RingProgram.ternary_baseWidth]
    have h : (2*t+1)^2 ≤ 4*(t+1)^2 := by
      calc
        (2*t+1)^2 ≤ (2*(t+1))^2 := Nat.pow_le_pow_left (show 2*t+1 ≤ 2*(t+1) by omega) 2
        _ = _ := by ring
    nlinarith [Nat.mul_le_mul_left (52000*(d+1)^5) h]
  · simpa only [preparedStore, modelTable, c, modelCoefficients_get] using he

/-- Every nonlocal register and stack is preserved by the actual lifted call. -/
theorem table_program_lifted {R S : ℕ} (ρ : Fin 8 → Fin R) (σ : Fin 42 → Fin S)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (frame : StructuredProgram.State R S)
    (t : ℕ) {d : ℕ} (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (ho : BinaryArithmetic.toNat cache.one.val < 3^t)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth 3 t) (hdegree : s.degree.length = d) :
    ∃ n ≤ 208000*(d+1)^5*(t+1)^2, ∃ rf,
      Eval (.call (ProgramLinking.liftProgram Machine.program ρ σ)) n
        (embedState ρ σ frame (Machine.state regs
          (initialStore s (modelCoefficients t a) cache.one cache.zero cache.minusOne) []))
        (embedState ρ σ frame (Machine.state rf
          (preparedStore 3 t M cache (modelCoefficients t a) s)
          (modelTable t a M cache))) := by
  obtain ⟨rf, n, hn, he⟩ := table_program_run t hd a M cache hz ho s regs hmod hw hdegree
  exact ⟨n, hn, rf, eval_call_lifted Machine.program ρ σ frame hρ hσ he⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramNodes.lean -/

/-! Physical node generation and record framing at the ring-setup ports. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpLiftRing

abbrev nodesCall : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram RingNodeProgram.preparedProgram
    (registers 8 (by decide)) nodes)

def nodeFramePorts : Fin 9 → Fin 640 := ![256,280,295,296,297,298,299,306,300]

theorem nodeFramePorts_injective : Function.Injective nodeFramePorts := by decide

abbrev nodeFramesCall : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram SubexpTaylorFrames.program
    (registers 5 (by decide)) nodeFramePorts)

def nodeWords (t d Q : ℕ) : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d) :=
  (List.finRange Q).map fun i => RingNodeProgram.nodeCode t d (i.val+1)

@[simp] theorem nodeWords_length (t d Q : ℕ) : (nodeWords t d Q).length = Q := by
  simp [nodeWords]

theorem nodesCall_eval (a : Data) (r : Fin 8 → Bool) (t : ℕ) (ht : 0 < t)
    (rank arity : List Bool)
    (ha : projectState (registers 8 (by decide)) nodes a =
      SubexpFieldRowPreparation.data r (List.replicate (baseWidth 3 t) false)
        rank arity [] [] []) :
    ∃ n ≤ RingNodeProgram.budget (baseWidth 3 t) rank.length arity.length
      (BinaryArithmetic.toNat rank)+5, ∃ rf finalRank,
      Eval nodesCall n a
        (embedState (registers 8 (by decide)) nodes a
          (SubexpFieldRowPreparation.data rf
            (true :: true :: List.replicate (baseWidth 3 t-2) false)
            finalRank arity [] []
            ((nodeWords t arity.length (BinaryArithmetic.toNat rank)).map RingProgram.flat).flatten)) ∧
      CounterPrograms.value finalRank = 0 ∧ finalRank.length = rank.length := by
  obtain ⟨rf,last,⟨n,hn,he⟩,hv,hl⟩ := RingNodeProgram.preparedProgram_nodes r t ht rank arity
  have he' := eval_call_from_state RingNodeProgram.preparedProgram
    (registers 8 (by decide)) nodes a (registers_injective 8 (by decide)) nodes_injective
    (ha.symm ▸ he)
  refine ⟨n,hn,rf,last,?_,hv,hl⟩
  simpa only [nodesCall,nodeWords,List.map_map,List.flatMap_def,Function.comp_def] using he'

theorem nodeFramesCall_eval (a : Data) (r : Fin 5 → Bool) (t d Q : ℕ)
    (width : List Bool) (hw : width.length = d * baseWidth 3 t)
    (ha : projectState (registers 5 (by decide)) nodeFramePorts a =
      SubexpTaylorFrames.state r
        (SubexpTaylorFrames.data width Q
          (((nodeWords t d Q).map RingProgram.flat).flatten) [])) :
    ∃ rf, Eval nodeFramesCall (Q*(28*width.length+33)+11) a
      (embedState (registers 5 (by decide)) nodeFramePorts a
        (SubexpTaylorFrames.state rf
          {SubexpTaylorFrames.data width 0 [] [] with
            output := Encoding.encodeList id ((nodeWords t d Q).map RingProgram.flat)})) := by
  obtain ⟨rf,he⟩ := LeafProgram.NodeFrames.ringWords_trace width hw (nodeWords t d Q) r
  simp only [nodeWords_length] at he
  exact ⟨rf,eval_call_from_state SubexpTaylorFrames.program
    (registers 5 (by decide)) nodeFramePorts a (registers_injective 5 (by decide))
    nodeFramePorts_injective (ha.symm ▸ he)⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramConstants.lean -/

/-! Actual constant-vector and idempotent calls in the setup workspace. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev constantCall (out : Fin 640) : Cmd 32 640 :=
  .call (ProgramLinking.liftProgram LeafProgram.Constants.program
    (registers 8 (by decide)) (constant out))

theorem constantCall_eval (a : Data) (out : Fin 640)
    (hinj : Function.Injective (constant out))
    {B : ℕ} (d : ℕ) (seed zeroWord : Word B) (s : RingProgramTable.Store)
    (r : Fin 8 → Bool) (hd : s.degree.length=d)
    (ha : projectState (registers 8 (by decide)) (constant out) a =
      RingProgramTable.state r (LeafProgram.Constants.input s seed zeroWord)) :
    ∃ n ≤ LeafProgram.Constants.budget B d+1, ∃ rf,
      Eval (constantCall out) n a
        (embedState (registers 8 (by decide)) (constant out) a
          (RingProgramTable.state rf (LeafProgram.Constants.output s d seed zeroWord))) := by
  obtain ⟨rf,n,hn,he⟩ := LeafProgram.Constants.program_run d seed zeroWord s r hd
  exact ⟨n,hn,rf,eval_call_from_state LeafProgram.Constants.program
    (registers 8 (by decide)) (constant out) a (registers_injective 8 (by decide))
    hinj (ha.symm ▸ he)⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
