import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryDegreeRing
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryConstruct

namespace OAI.Algorithms

/-! Exact unary degree bytes of the actual query arithmetic, obtained from its
existing execution. No executable command or preparation record changes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem arithmetic_degree (base out : Data) (n : ℕ) (he : Eval arithmetic n base out)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀i,(base.stacks i).length ≤ W)
    (hv : ∀i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2)
    (h728 : base.stacks 728=[]) : out.stacks 204=List.replicate (m.val 34) true := by
  obtain ⟨nr,hnr,e,M,cache,u,b,hr,hp,hlow,h713,h714,h715,h716,h717,hprivate,hhigh,
    hcollector,hregs,hlowBlank,hdegree⟩ :=
    Ring.command_eval_degree base m w r hs ha W V L hinit hv hw ht hd hexp
  have hf728 : b.stacks 728=base.stacks 728 := hhigh _ (by decide) (by decide) (by decide)
  have hbwidth : ∀i,(b.stacks i).length ≤ W+Ring.budget m W V L+1 := by
    intro i
    have hi := LeafRingSetupProgram.Interpolation.eval_width hr hinit i
    omega
  obtain ⟨nd,hnd,last,he',hout,hinv,hdregs⟩ :=
    LayoutDenominatorProgramQuery.produced_command_eval b m ht hd M cache u e hp hlow
      (fun i hi hj => hprivate i hi (by omega)) (hf728.trans h728) _ hbwidth
  have heq := SubexpPrimeProgram.eval_result_unique he (hr.seq he') 0 0
  rw [heq,hout,Function.update_of_ne (by decide : (204:Fin 768)≠728)]
  exact hdegree

theorem Preparation.degree {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (h728 : a.stacks 728=[]) :
    p.out.stacks 204=List.replicate ((Execute.guardedModel (q.input k) p.lengths).val 34) true := by
  have hbank := ring_bank_of_frame p.front p.packed p.bankWords _ p.frontOutput.bank
    (fun i hi hj => p.packingFrame i (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))
  have hf728 : p.front.stacks 728=a.stacks 728 := p.frontOutput.frame _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  have hp728 : p.packed.stacks 728=[] :=
    (p.packingFrame _ (by decide) (by decide) (by decide)).trans (hf728.trans h728)
  let ms := Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)
  exact arithmetic_degree p.packed p.out p.arithmeticSteps p.arithmeticExecution
    _ p.bankWords _ p.frontOutput.shape hbank
    (Finset.univ.sup (fun i => (p.packed.stacks i).length))
    (Finset.univ.sup ms.val) (Finset.univ.sup ms.len)
    (fun i => Finset.le_sup (f := fun j : Fin 768 => (p.packed.stacks j).length) (Finset.mem_univ i))
    (fun i => Finset.le_sup (Finset.mem_univ i))
    (fun i => Finset.le_sup (Finset.mem_univ i))
    (ring_precision_pos (q.input k) p.lengths hg) (ring_degree_pos (q.input k) p.lengths hg)
    (ring_exponent (q.input k) p.lengths hg) hp728

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
