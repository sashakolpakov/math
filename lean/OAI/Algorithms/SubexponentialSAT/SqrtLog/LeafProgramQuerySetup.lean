import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryReference
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryBranches
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryGuard
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidual
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQueryCode

namespace OAI.Algorithms

/-! One concrete per-query instruction table. The frontend guard is tested
before packing or ring allocation. The successful path prepares shared data
once, evaluates every high assignment, and returns the summed integer on323.
Both paths perform the same paid reclamation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

def prepare : Code := .seq Samples.prepare Count.Prepare.command
def prepared (a : Data) : Data := Count.Prepare.output (Samples.prepared a)
def prepareCost (a : Data) : ℕ :=
  Samples.prepareCost a+Count.Prepare.budget (Samples.prepared a)

private theorem nativeClean_190 : (190 : Fin 320) ∉
    ReconstructionProgram.NativeState.cleanPorts := by
  simp [ReconstructionProgram.NativeState.cleanPorts,
    ReconstructionProgram.NativeState.workingClean,
    ReconstructionProgram.Middle.cleanPorts,
    ReconstructionProgram.CofactorOuter.cleanPorts,
    ReconstructionProgram.Scalar.cleanPorts,
    ReconstructionProgram.Horner.cleanPorts,
    SubexpCRTOuterProgram.initialCleanPorts, CRTLocalProgram.localWork,
    SubexponentialSAT.SubexpConvolutionControl.bufferPorts,
    SubexpCRTOuterProgram.localPorts]

private theorem nativeClean_191 : (191 : Fin 320) ∉
    ReconstructionProgram.NativeState.cleanPorts := by
  simp [ReconstructionProgram.NativeState.cleanPorts,
    ReconstructionProgram.NativeState.workingClean,
    ReconstructionProgram.Middle.cleanPorts,
    ReconstructionProgram.CofactorOuter.cleanPorts,
    ReconstructionProgram.Scalar.cleanPorts,
    ReconstructionProgram.Horner.cleanPorts,
    SubexpCRTOuterProgram.initialCleanPorts, CRTLocalProgram.localWork,
    SubexponentialSAT.SubexpConvolutionControl.bufferPorts,
    SubexpCRTOuterProgram.localPorts]

private theorem countPrepare_190 : (190 : Fin 768) ∉ Count.Prepare.ports := by
  intro h
  simp only [Count.Prepare.ports, List.mem_dedup, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp h
    have hj190 : j = (190 : Fin 320) := by
      apply Fin.ext
      have hv := congrArg Fin.val hji
      simpa [Count.crtStacks] using hv
    subst j
    rcases List.mem_append.mp hj with hj | hj
    · exact nativeClean_190 hj
    · simp [ReconstructionProgram.InputReady.emptyPorts] at hj
  · simp at h

private theorem countPrepare_191 : (191 : Fin 768) ∉ Count.Prepare.ports := by
  intro h
  simp only [Count.Prepare.ports, List.mem_dedup, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp h
    have hj191 : j = (191 : Fin 320) := by
      apply Fin.ext
      have hv := congrArg Fin.val hji
      simpa [Count.crtStacks] using hv
    subst j
    rcases List.mem_append.mp hj with hj | hj
    · exact nativeClean_191 hj
    · simp [ReconstructionProgram.InputReady.emptyPorts] at hj
  · simp at h

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) :=
  (Samples.prepare_eval a).seq (Count.Prepare.command_eval (Samples.prepared a))

theorem prepared_count_empty (a : Data) (i : Fin 768) (hi : i∈Count.Prepare.ports) :
    (prepared a).stacks i=[] := by
  exact Count.Prepare.output_port _ _ hi

theorem prepared_190 (a : Data) : (prepared a).stacks 190=[] := by
  unfold prepared
  rw [Count.Prepare.output_frame _ _ countPrepare_190 (by norm_num)]
  simp [Samples.prepared_stacks]

theorem prepared_191 (a : Data) : (prepared a).stacks 191=[] := by
  unfold prepared
  rw [Count.Prepare.output_frame _ _ countPrepare_191 (by norm_num)]
  simp [Samples.prepared_stacks]

def success : Code := .seq PackingCallerProgram.command
  (.seq arithmetic (.seq prepare (branches Residual.command)))

def command (k : ℕ) : Code :=
  guarded k success

def marked (k : ℕ) : Code := .seq markInput (command k)
def accepted (k : ℕ) : Code := .seq noMarkInput (command k)

def program (k : ℕ) := compiled (command k) 700 323
def markedProgram (k : ℕ) := compiled (marked k) 321 323
def acceptedProgram (k : ℕ) := compiled (accepted k) 700 323

/-- A composition lemma for the checked service endpoints. The later native
contract instantiates these endpoints from their concrete byte interfaces. -/
theorem success_eval (a packed denominator : Data) (np nr count B width W : ℕ)
    (hp : Eval PackingCallerProgram.command np a packed)
    (hr : Eval arithmetic nr packed denominator)
    (ready : (Fin 763 → List Bool) → Prop)
    (ctx : Marked.Wide.BranchContext Residual.command
      (Marked.Wide.maskCopied (prepared denominator)) ready count B width)
    (htmp : (prepared denominator).stacks 339=[])
    (hw : ∀i,((prepared denominator).stacks i).length ≤ W) :
    ∃ n middle, n ≤ np+nr+prepareCost denominator+branchBudget (prepared denominator) B W ∧
      Eval success n a (cleaned middle) ∧
      BinaryArithmetic.toNat ((cleaned middle).stacks 323)=count ∧
      ((cleaned middle).stacks 323).length ≤ width ∧
      (∀i,¬Protected i → (cleaned middle).stacks i=[]) ∧
      (cleaned middle).regs 16=false ∧ (cleaned middle).regs 17=true ∧
      (cleaned middle).regs 18=false ∧ ready (Marked.Wide.workspace middle) := by
  obtain ⟨nb,middle,hnb,he,_,_,hv,hl,hclean,h16,h17,h18,hready⟩ :=
    branches_eval Residual.command (prepared denominator) ready count B width W ctx htmp hw
  exact ⟨np+(nr+(prepareCost denominator+nb)),middle,by omega,
    hp.seq (hr.seq ((prepare_eval denominator).seq he)),hv,hl,hclean,h16,h17,h18,hready⟩

theorem command_true_eval (k : ℕ) (a front out : Data) (nf ns : ℕ)
    (hf : Eval (LeafQueryFrontend.frontend k) nf a front)
    (hg : front.regs 8=true) (hs : Eval success ns front out) :
    Eval (command k) (nf+(ns+1)) a out := hf.seq (.ite_true hg hs)

theorem command_false_eval (k : ℕ) (a front : Data) (nf : ℕ)
    (hf : Eval (LeafQueryFrontend.frontend k) nf a front)
    (hg : front.regs 8=false) :
    Eval (command k) (nf+(cleanupCost front+1)) a (cleaned front) :=
  hf.seq (.ite_false hg (cleanup_eval front))

theorem program_runs_of_eval (k : ℕ) (a b : Data) (n : ℕ)
    (he : Eval (command k) n a b) :
    RunsIn (program k) (n+1)
      (a.withPC (some (program k).entry)) (b.withPC none) :=
  ⟨n+1,le_rfl,compiled_halt_trace he 700 323⟩

theorem primitive_of_eval (k : ℕ) (a b : Data) (n : ℕ)
    (he : Eval (command k) n a b) :
    Computation.RunsIn (primitive (program k)).step
      (primitiveOverhead (program k)*(n+1))
      (primitiveCfg (program k) (a.withPC (some (program k).entry)))
      (primitiveCfg (program k) (b.withPC none)) :=
  primitive_execution (program k) (program_runs_of_eval k a b n he)

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end

end OAI.Algorithms
