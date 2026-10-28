import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryRing
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram

namespace OAI.Algorithms

/-! Transport an exact producer tape property through the existing interpolation
and denominator phases. This is a proof about the unchanged command. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafRingSetupProgram

theorem command_property (base out : Query.Data) (n : ℕ) (he : Eval command n base out)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters
      (projectState wideRegisters wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀i,(base.stacks i).length ≤ W)
    (hv : ∀i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2)
    (i : Fin 768) (hi : i.val < 340) (word : List Bool)
    (hprop : ∀ nr b, Eval producerWideCall nr base b → b.stacks i=word) :
    out.stacks i=word := by
  obtain ⟨nr,hnr,e,M,cache,u,her,hp,hregs,hhigh,hlow⟩ :=
    producerProgram_lifted base (projectState wideRegisters wideStacks base) rfl m w r hs ha
      W V L (fun i => hinit (wideStacks i)) hv hw ht hd
  let b := embedState wideRegisters wideStacks base e
  have hb (i : Fin 640) : b.stacks (wideStacks i)=e.stacks i :=
    embedState_stack _ _ _ _ wideStacks_injective i
  have hinput := Interpolation.inputs_of_produced b e m hd M cache u hp hb hexp
  have hflat : b.stacks 256=(nodeWords (m.val 33) (m.val 34) (m.val 21)).flatMap RingProgram.flat := by
    rw [show b.stacks 256=e.stacks 256 from hb 256,hp.flatNodes]
    rw [List.flatMap_def]
  have hwidth : ∀i,(b.stacks i).length ≤ W+(producerBudget m W V L+1)+1 := by
    intro i
    have hh := Interpolation.eval_width her hinit i
    dsimp only [b]
    omega
  have hpos : 0 < m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33) := by
    apply Nat.mul_pos hd
    unfold SubexpLiftRing.baseWidth
    exact Nat.mul_pos ht (Nat.succ_pos _)
  obtain ⟨ni,hni,last,hei,h713,h714,h715,h716,h717,hprivate,hframe,hiregs⟩ :=
    Interpolation.command_eval b (m.val 33) (IrreducibleSearch.data hd) M cache hp.caches.canonical
      (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero) hpos
      (nodeWords (m.val 33) (m.val 34) (m.val 21)) hinput hflat
      (W+(producerBudget m W V L+1)+1) hwidth
  have outside (i : Fin 768) (hi : i.val < 340 ∨ 660 ≤ i.val) : i∉Interpolation.privatePorts := by
    simp only [Interpolation.privatePorts,List.mem_map,List.mem_finRange,true_and,not_exists]
    intro j hj
    have hh := congrArg Fin.val hj
    dsimp [Interpolation.localPorts] at hh
    omega
  have heq := SubexpPrimeProgram.eval_result_unique he (her.seq hei) 0 0
  rw [heq]
  apply (hframe i (outside i (Or.inl hi)) ?_ ?_).trans (hprop nr b her)
  · intro h
    have hh : i.val=699 := congrArg Fin.val h
    omega
  · intro h
    have hh : 340 ≤ i.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl <;> decide
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring

end OAI.Algorithms
