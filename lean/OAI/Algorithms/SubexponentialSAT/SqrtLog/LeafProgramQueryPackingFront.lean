import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryFrontState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryRingModel

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram MulticolorTypes Subexp

/-- Frontend and packing are both executed on the actual input masters.
The input-only frontend bound and the native packing bound remain separate. -/
theorem frontend_packing (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hr : q.Ready a) (ho : q.OutputEmpty a) (hspare : PackingSpare a)
    (hg : Guard (q.input k)) (W : ℕ) (hw : ∀i,(a.stacks i).length ≤ W) :
    let p := packingProblem q k hg
    ∃ nf front l bw, ∃ w : Word p.r p.Q, ∃ tail : List (Word p.r p.Q), ∃ np packed,
      Eval (LeafQueryFrontend.frontend k) nf a front ∧ nf ≤ q.inputBudget k ∧
      FrontState q k a front l bw ∧ (w::tail).Nodup ∧ (∀z,z∈w::tail) ∧
      Eval PackingCallerProgram.command np front packed ∧
      np+1 ≤ PackingCallerProgram.budget front p w tail ∧
      packed.stacks=(PackingCallerProgram.result front p w tail).stacks ∧
      projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
        (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks packed)=
        Bank.state (packed.regs ∘ Exports.bankRegs) bw ∧
      (∀i : Fin 768,(i.val < 417 ∨ 481 ≤ i.val) →
        (i.val < 128 ∨ 142 ≤ i.val) → (i.val < 730 ∨ 744 ≤ i.val) → packed.stacks i=front.stacks i) ∧
      (∀i : Fin 40,16 ≤ i.val → packed.regs i=front.regs i) ∧
      (∀i,(packed.stacks i).length ≤ W+q.inputBudget k+PackingCallerProgram.budget front p w tail) ∧
      (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q := by
  dsimp only
  obtain ⟨nf,front,l,bw,hf,hfn,hfs⟩ := front_state q k a hv hr ho hspare
  have hfw : ∀i,(front.stacks i).length ≤ W+q.inputBudget k := by
    intro i
    exact (eval_width hf W hw i).trans (Nat.add_le_add_left hfn W)
  obtain ⟨w,tail,np,packed,hn,hall,hpn,hp,hbytes,hbank,hframe,hregs,hwidth,hrows⟩ :=
    packing_run q k front hg l bw (front.regs ∘ Exports.bankRegs) hfs.exported
      hfs.scopes hfs.forward hfs.ambient hfs.privateEmpty hfs.spare hfs.bank _ hfw
  exact ⟨nf,front,l,bw,w,tail,np,packed,hf,hfn,hfs,hn,hall,hp,hpn,hbytes,hbank,hframe,hregs,hwidth,hrows⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
