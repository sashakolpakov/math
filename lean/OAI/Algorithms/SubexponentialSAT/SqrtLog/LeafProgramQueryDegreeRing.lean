import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryRing
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramDegreeWide

namespace OAI.Algorithms

/-! Extra exact-byte certificate for the unchanged ring/interpolation command. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafRingSetupProgram

theorem command_eval_degree (base : Query.Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (registers 8 (by decide)) parameters
      (projectState wideRegisters wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀i,(base.stacks i).length ≤ W)
    (hv : ∀i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2) :
    ∃ n ≤ budget m W V L, ∃ e : LeafRingSetupProgram.Data,
      ∃ (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)), ∃ out : Query.Data,
      Eval command n base out ∧ Produced m hd M cache u e ∧
      (∀i : Fin 640,i.val < 340 → out.stacks (wideStacks i)=e.stacks i) ∧
      out.stacks 713=InterpolationCacheProgram.inverseBytes (m.val 33) (IrreducibleSearch.data hd)
        M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
        (nodeWords (m.val 33) (m.val 34) (m.val 21)) ∧
      out.stacks 714=InterpolationCacheProgram.negativeBytes (m.val 33) (IrreducibleSearch.data hd)
        M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
        (nodeWords (m.val 33) (m.val 34) (m.val 21)) ∧
      out.stacks 715=InterpolationCacheProgram.differenceBytes (m.val 33) (IrreducibleSearch.data hd)
        M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
        (nodeWords (m.val 33) (m.val 34) (m.val 21)) ∧
      out.stacks 716=List.replicate (m.val 21*(m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33))) true ∧
      out.stacks 717=List.replicate (m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33)) true ∧
      (∀i : Fin 768,340 ≤ i.val → i.val < 660 → out.stacks i=[]) ∧
      (∀i : Fin 768,660 ≤ i.val → i≠699 → i∉([713,714,715,716,717] : List (Fin 768)) →
        out.stacks i=base.stacks i) ∧
      (∀i : Fin 768,320 ≤ i.val → i.val < 340 → out.stacks i=base.stacks i) ∧
      (∀i : Fin 40,16 ≤ i.val → i.val < 24 → out.regs i=base.regs i) ∧
      (∀i : Fin 768,i.val < 190 → base.stacks i=[] → out.stacks i=[]) ∧
      out.stacks 204=List.replicate (m.val 34) true := by
  obtain ⟨nr,hnr,e,M,cache,u,her,hp,hregs,hhigh,hlow⟩ :=
    producerProgram_lifted base (projectState wideRegisters wideStacks base) rfl m w r hs ha
      W V L (fun i => hinit (wideStacks i)) hv hw ht hd
  let b := embedState wideRegisters wideStacks base e
  have hb (i : Fin 640) : b.stacks (wideStacks i)=e.stacks i :=
    embedState_stack _ _ _ _ wideStacks_injective i
  have hi := Interpolation.inputs_of_produced b e m hd M cache u hp hb hexp
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
  obtain ⟨ni,hni,out,hei,h713,h714,h715,h716,h717,hprivate,hframe,hiregs⟩ :=
    Interpolation.command_eval b (m.val 33) (IrreducibleSearch.data hd) M cache hp.caches.canonical
      (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero) hpos
      (nodeWords (m.val 33) (m.val 34) (m.val 21)) hi hflat
      (W+(producerBudget m W V L+1)+1) hwidth
  have outside (i : Fin 768) (hi : i.val < 340 ∨ 660 ≤ i.val) : i∉Interpolation.privatePorts := by
    simp only [Interpolation.privatePorts,List.mem_map,List.mem_finRange,true_and,not_exists]
    intro j hj
    have hh := congrArg Fin.val hj
    dsimp [Interpolation.localPorts] at hh
    omega
  refine ⟨nr+ni,?_,e,M,cache,u,out,her.seq hei,hp,?_,h713,h714,h715,?_,h717,?_,?_,?_,?_,?_,?_⟩
  · simp only [nodeWords_length] at hni
    dsimp only [budget]
    omega
  · intro i hi
    exact (hframe (wideStacks i) (outside _ (Or.inl hi))
      (by intro h; have := congrArg Fin.val h; dsimp [wideStacks] at this; omega)
      (by simp only [List.mem_cons,List.not_mem_nil,or_false];
          intro h; rcases h with h|h|h|h|h <;>
            have hh := congrArg Fin.val h <;> dsimp [wideStacks] at hh <;> omega)).trans (hb i)
  · simpa only [nodeWords_length] using h716
  · intro i hlo hhi
    let j : Fin 320 := ⟨i.val-340,by omega⟩
    have hj : Interpolation.localPorts j=i := by
      apply Fin.ext
      dsimp [Interpolation.localPorts,j]
      omega
    rw [← hj]
    exact hprivate _ (Interpolation.privatePorts_mem j)
  · intro i hi h699 ho
    exact (hframe i (outside i (Or.inr hi)) h699 ho).trans (hhigh i (by omega))
  · intro i hlo hhi
    let j : Fin 640 := ⟨i.val,by omega⟩
    have hj : wideStacks j=i := Fin.ext rfl
    have hf := hframe i (outside i (Or.inl hhi))
      (by intro h; have hh : i.val=699 := congrArg Fin.val h; omega)
      (by
        intro h
        have hlarge : 340 ≤ i.val := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl|rfl|rfl|rfl|rfl <;> decide
        omega)
    exact hf.trans (by simpa only [hj] using hlow j hlo hhi)
  · intro i hlo hhi
    exact (hiregs i hlo (by omega)).trans (hregs i hlo hhi)

  · intro i hi hz
    have hbz := LowFrame.producerWideCall_empty base b nr her m w r hs ha W V L
      hinit hv hw ht hd i hi hz
    apply Eq.trans (hframe i (outside i (Or.inl (by omega))) ?_ ?_) hbz
    · intro h
      have hh : i.val=699 := congrArg Fin.val h
      omega
    · intro h
      have hh : 190 ≤ i.val := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl|rfl <;> decide
      omega

  · have hdg := producerWideCall_degree base b nr her m w r hs ha W V L hinit hv hw ht hd
    exact (hframe 204 (outside _ (Or.inl (by decide))) (by decide) (by decide)).trans hdg

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring

end OAI.Algorithms
