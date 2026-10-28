import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPreparationState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmeticConstruct

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram MulticolorTypes Subexp

 theorem prepare_native (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hr : q.Ready a) (ho : q.OutputEmpty a) (hspare : PackingSpare a)
    (hg : Guard (q.input k)) (h728 : a.stacks 728=[])
    (W V L : ℕ) (hwidth : ∀i,(a.stacks i).length ≤ W)
    (hvalues : ∀l i,(Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).val i ≤ V)
    (hlengths : ∀i,(Circuit.result Serialization.code (Execute.guardedModel (q.input k) (q.inputLengths k))).len i ≤ L) :
    Nonempty (Preparation q k a hg W V L) := by
  obtain ⟨nf,front,l,bw,w,tail,np,packed,hf,hfn,hfs,hn,hall,hp,hpn,hbytes,hbank,hframe,hregs,hw,hrows⟩ :=
    frontend_packing q k a hv hr ho hspare hg W hwidth
  have hf728 : front.stacks 728=a.stacks 728 := hfs.frame _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  have hp728 : packed.stacks 728=[] :=
    (hframe _ (by decide) (by decide) (by decide)).trans (hf728.trans h728)
  have hcutoff := packed_cutoff (q.input k) l front packed (packingProblem q k hg) w tail
    (packing_empty front hfs.privateEmpty hfs.spare) hfs.exported hbytes
  obtain ⟨arithmeticData⟩ :=
    constructArithmetic packed (Execute.guardedModel (q.input k) l) bw (packed.regs ∘ Exports.bankRegs)
      hfs.shape hbank _ V L hw (hvalues l) (by simpa only [hfs.canonicalLengths] using hlengths)
      (ring_precision_pos (q.input k) l hg) (ring_degree_pos (q.input k) l hg)
      (ring_exponent (q.input k) l hg) hp728
  exact ⟨{
    lengths := l, bankWords := bw, front := front, frontSteps := nf,
    frontExecution := hf, frontTime := hfn, frontOutput := hfs,
    firstWord := w, remainingWords := tail, alphabetOrder := hrows,
    alphabetNodup := hn, alphabetComplete := hall,
    packed := packed, packingSteps := np, packingExecution := hp, packingTime := hpn,
    packingBytes := hbytes, packingFrame := hframe, packingRegisters := hregs, cutoff := hcutoff,
    arithmeticData := arithmeticData }⟩

 theorem Preparation.execution {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L) :
    Eval (guarded k (.seq PackingCallerProgram.command arithmetic))
      (p.frontSteps+(p.packingSteps+p.arithmeticSteps+1)) a p.out :=
  p.frontExecution.seq (.ite_true (p.frontOutput.guard.mpr hg)
    (p.packingExecution.seq p.arithmeticExecution))

theorem Preparation.protected_frame {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (i : Fin 768) (hi : Protected i) : p.out.stacks i=a.stacks i := by
  have hp : p.packed.stacks i=p.front.stacks i := by
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hi
    all_goals apply p.packingFrame
    all_goals first | decide | (right; omega)
  exact (p.arithmeticOutput.protected_frame i hi).trans
    (hp.trans (p.frontOutput.protected_frame i hi))

theorem Preparation.register_frame {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (i : Fin 40) (hlo : 16 ≤ i.val) (hhi : i.val < 24) : p.out.regs i=a.regs i :=
  (p.arithmeticOutput.registerFrame i hlo hhi).trans
    ((p.packingRegisters i hlo).trans (p.frontOutput.registerFrame i (by omega)))

theorem Preparation.output_width {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,(p.out.stacks i).length ≤ W+p.frontSteps+p.packingSteps+p.arithmeticSteps := by
  intro i
  have h := eval_width (p.frontExecution.seq (p.packingExecution.seq p.arithmeticExecution)) W hw i
  change (p.arithmeticData.out.stacks i).length ≤ W+p.frontSteps+p.packingSteps+p.arithmeticData.steps
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
