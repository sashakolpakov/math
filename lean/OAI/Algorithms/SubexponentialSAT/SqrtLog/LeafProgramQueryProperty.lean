import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPropertyRing
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryConstruct

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

theorem arithmetic_property (base out : Data) (n : ℕ) (he : Eval arithmetic n base out)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀i,(base.stacks i).length ≤ W)
    (hv : ∀i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2)
    (h728 : base.stacks 728=[]) (i : Fin 768) (hi : i.val < 340) (word : List Bool)
    (hprop : ∀ nr b, Eval LeafRingSetupProgram.producerWideCall nr base b → b.stacks i=word) :
    out.stacks i=word := by
  obtain ⟨nr,hnr,e,M,cache,u,b,hr,hp,hlow,h713,h714,h715,h716,h717,hprivate,hhigh,
    hcollector,hregs,hlowBlank⟩ :=
    Ring.command_eval base m w r hs ha W V L hinit hv hw ht hd hexp
  have hproperty := Ring.command_property base b nr hr m w r hs ha W V L hinit hv hw ht hd hexp i hi word hprop
  have hf728 : b.stacks 728=base.stacks 728 := hhigh _ (by decide) (by decide) (by decide)
  have hbwidth : ∀i,(b.stacks i).length ≤ W+Ring.budget m W V L+1 := by
    intro i
    have hi := LeafRingSetupProgram.Interpolation.eval_width hr hinit i
    omega
  obtain ⟨nd,hnd,last,he',hout,hinv,hdregs⟩ :=
    LayoutDenominatorProgramQuery.produced_command_eval b m ht hd M cache u e hp hlow
      (fun i hi hj => hprivate i hi (by omega)) (hf728.trans h728) _ hbwidth
  have heq := SubexpPrimeProgram.eval_result_unique he (hr.seq he') 0 0
  have hne : i≠728 := by intro h; have hh : i.val=728 := congrArg Fin.val h; omega
  rw [heq,hout,Function.update_of_ne hne]
  exact hproperty

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
