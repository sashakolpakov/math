import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafMarkedProgramWideValueCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgramWideNative

namespace OAI.Algorithms

/-! The marked collector's query is a paid mask copy followed by exhaustive
branching. Its proof interface is the residual program invariant; it does not
accept an execution oracle or a list of precomputed full counts. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def maskCopy : Code := .call (StackRoutines.copyProgram 338 333 339 0 1)
def maskCopied (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 338 333 a.stacks⟩

theorem maskCopy_eval (a : Data) (ht : a.stacks 339 = []) :
    Eval maskCopy (7*(a.stacks 338).length+5) a (maskCopied a) :=
  Eval.call _ (ListRegisterProgram.copy_run 338 333 339 0 1
    (by decide) (by decide) (by decide) (by decide) a.regs a.stacks ht)

@[simp] theorem maskCopied_frame (a : Data) (i : Fin 768) (hi : i ≠ 333) :
    (maskCopied a).stacks i = a.stacks i := by
  simp [maskCopied,StackRoutines.copyStacks,hi]

theorem maskCopied_mask (a : Data) (he : a.stacks 333 = []) :
    (maskCopied a).stacks 333 = a.stacks 338 := by
  simp [maskCopied,StackRoutines.copyStacks,he]

def nativeQuery (residual : Code) : Code := .seq maskCopy (LeafBranchProgram.Wide.command residual)

def branchTime (a : Data) (budget width refBound : ℕ) : ℕ :=
  let h := HighIncidenceProgram.Branches.trueCount (a.stacks 333)
  let N := 2^h
  11*(a.stacks 333).length+5 +
    (N*(budget+16*(N*(width+1)+1)+28*h+15)+2) +
    (2*(4*h+1)+6*(N*(width+1))+2*refBound+15)

/-- Local facts supplied by the concrete residual query. All data-dependent
objects here occur only in the proof; `nativeQuery residual` is fixed. -/
structure BranchContext (residual : Code) (a : Data)
    (ready : (Fin 763 → List Bool) → Prop) (count budget width : ℕ) where
  inv : Data → Prop
  stepBudget : ℕ
  stepWidth : ℕ
  referenceBound : ℕ
  value : ℕ → ℕ
  counterStable : CounterForPrograms.FrameStable LeafBranchProgram.Wide.fixedPorts.counter (fun _ => inv)
  massStable : LeafBranchProgram.MassStable LeafBranchProgram.Wide.fixedPorts inv
  residualSpec : LeafBranchProgram.ResidualSpec LeafBranchProgram.Wide.fixedPorts residual
    (List.replicate (HighIncidenceProgram.Branches.trueCount (a.stacks 333)) 1)
    inv stepBudget stepWidth value
  initialized : ∀ regs, inv (LeafBranchProgram.Wide.initialized a regs (a.stacks 333))
  referenceLength : ∀ b, inv b → (b.stacks 321).length ≤ referenceBound
  counterEmpty : a.stacks 330 = []
  counterScratchEmpty : a.stacks 331 = []
  massEmpty : a.stacks 332 = []
  nextEmpty : a.stacks 323 = []
  addScratchEmpty : a.stacks 324 = []
  sourceFrame : ∀ b, inv b → b.stacks 320 = a.stacks 320
  accumulatorFrame : ∀ b, inv b → b.stacks 322 = a.stacks 322
  finalReady : ∀ b, inv b → (LeafBranchProgram.Wide.finished b).stacks 331 = [] →
    ready (workspace (LeafBranchProgram.Wide.finished b))
  fullCount : LeafBranchProgram.rankSum value 0
    (2^HighIncidenceProgram.Branches.trueCount (a.stacks 333)) = count
  outputLength : 2^HighIncidenceProgram.Branches.trueCount (a.stacks 333)*(stepWidth+1) ≤ width
  timeBound : branchTime a stepBudget stepWidth referenceBound ≤ budget

theorem branchContext_eval (residual : Code) (a : Data)
    (ready : (Fin 763 → List Bool) → Prop) (count budget width : ℕ)
    (ctx : BranchContext residual a ready count budget width) :
    ∃ n b, n ≤ budget ∧ ready (workspace b) ∧ b.stacks 320 = a.stacks 320 ∧
      b.stacks 322 = a.stacks 322 ∧ BinaryArithmetic.toNat (b.stacks 323) = count ∧
      (b.stacks 323).length ≤ width ∧ b.stacks 321 = [] ∧ b.stacks 324 = [] ∧
      b.regs 16 = false ∧ b.regs 17 = true ∧ b.regs 18 = false ∧
      Eval (LeafBranchProgram.Wide.command residual) n a b := by
  obtain ⟨n,b,he,hi,hs,hl,hv,ht⟩ := LeafBranchProgram.Wide.command_rankSum residual a ctx.inv
    ctx.stepBudget ctx.stepWidth ctx.referenceBound ctx.value ctx.counterStable ctx.massStable
    ctx.residualSpec ctx.initialized ctx.referenceLength ctx.counterEmpty ctx.counterScratchEmpty
    ctx.massEmpty ctx.nextEmpty ctx.addScratchEmpty
  have hempty := LeafBranchProgram.Wide.finished_empty b
  have hparser := LeafBranchProgram.Wide.finished_parser b
  refine ⟨n,LeafBranchProgram.Wide.finished b,ht.trans ctx.timeBound,
    ctx.finalReady b hi hs,?_,?_,hv.trans ctx.fullCount,hl.trans ctx.outputLength,
    hempty.1,hempty.2.1,hparser.1,hparser.2.1,hparser.2.2,he⟩
  · exact (LeafBranchProgram.Wide.finished_frame b 320 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (ctx.sourceFrame b hi)
  · exact (LeafBranchProgram.Wide.finished_frame b 322 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (ctx.accumulatorFrame b hi)

/-- One concrete residual command suffices for the outer collector. The mask
copy is inside that fixed query, so its full cost is paid for every reference. -/
theorem native_query_contract (residual : Code) (count queryCost width : List Bool → ℕ)
    (ready : (Fin 763 → List Bool) → Prop) (valid : List Bool → Prop)
    (contexts : ∀ bits tail (base : Data), valid bits → invariant ready base →
      let start := RecordPrograms.state recordPorts base false true false tail bits.reverse
      ∃ budget, start.stacks 339 = [] ∧ start.stacks 333 = [] ∧
        Nonempty (BranchContext residual (maskCopied start) ready (count bits) budget (width bits)) ∧
        7*(start.stacks 338).length+5+budget ≤ queryCost bits) :
    QueryValueContract (nativeQuery residual) count queryCost width ready valid := by
  intro bits tail base hv hb
  let start := RecordPrograms.state recordPorts base false true false tail bits.reverse
  obtain ⟨budget,htmp,hempty,⟨ctx⟩,hcost⟩ := contexts bits tail base hv hb
  obtain ⟨n,b,hn,hr,hs,ha,hv,hl,hp,ht,h16,h17,h18,he⟩ :=
    branchContext_eval residual (maskCopied start) ready (count bits) budget (width bits) ctx
  have hsource : b.stacks 320 = tail := by
    simpa [start,RecordPrograms.state,recordPorts] using hs
  have hacc : read b = read base := by
    simpa [read,start,RecordPrograms.state,recordPorts] using ha
  have hstate : RecordPrograms.state recordPorts b false true false tail [] = b :=
    RecordPrograms.state_eq_self recordPorts b _ _ _ _ _ h16 h17 h18 hsource hp
  refine ⟨7*(start.stacks 338).length+5+n,b,by dsimp only [start]; omega,hr,hacc,hv,hl,ht,?_⟩
  rw [hstate]
  exact (maskCopy_eval start htmp).seq he

end SubexponentialSAT.SqrtLog.LeafProgram.Marked.Wide

end OAI.Algorithms
