import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryRing
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

namespace OAI.Algorithms

/-! One actual arithmetic preparation per query: ring caches, interpolation
caches, then the inverse layout denominator. All three run before branching. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

 def arithmetic : Code := .seq Ring.command LayoutDenominatorProgramQuery.command

 def arithmeticBudget (m : Circuit.Model) (W V L R : ℕ) : ℕ :=
  Ring.budget m W V L+
    LayoutDenominatorProgramQuery.budget R (m.val 33) (m.val 34) (W+Ring.budget m W V L+1)

/-- The final arithmetic state remembers the exact generated cache state;
only port728 is added after the ring/interpolation program. -/
structure ArithmeticOutput (base out : Data) (m : Circuit.Model) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data) : Prop where
  produced : LeafRingSetupProgram.Produced m hd M cache u e
  low : ∀i : Fin 640,i.val < 340 → out.stacks (LeafRingSetupProgram.wideStacks i)=e.stacks i
  inverse : out.stacks 713=InterpolationCacheProgram.inverseBytes (m.val 33) (IrreducibleSearch.data hd)
    M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
    (LeafRingSetupProgram.nodeWords (m.val 33) (m.val 34) (m.val 21))
  negative : out.stacks 714=InterpolationCacheProgram.negativeBytes (m.val 33) (IrreducibleSearch.data hd)
    M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
    (LeafRingSetupProgram.nodeWords (m.val 33) (m.val 34) (m.val 21))
  difference : out.stacks 715=InterpolationCacheProgram.differenceBytes (m.val 33) (IrreducibleSearch.data hd)
    M cache (LeafProgram.Constants.constantCode (m.val 34) cache.minusOne cache.zero)
    (LeafRingSetupProgram.nodeWords (m.val 33) (m.val 34) (m.val 21))
  nodesLength : out.stacks 716=List.replicate (m.val 21*(m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33))) true
  width : out.stacks 717=List.replicate (m.val 34*SubexpLiftRing.baseWidth 3 (m.val 33)) true
  denominator : out.stacks 728=RingProgram.flat (LayoutDenominatorProgramQuery.value
    (m.val 33) (IrreducibleSearch.data hd) M cache u (base.stacks 740).length)
  privateEmpty : ∀i : Fin 768,340 ≤ i.val → i.val < 660 → out.stacks i=[]
  highFrame : ∀i : Fin 768,660 ≤ i.val → i≠699 →
    i∉([713,714,715,716,717,728] : List (Fin 768)) → out.stacks i=base.stacks i
  collectorFrame : ∀i : Fin 768,320 ≤ i.val → i.val < 340 → out.stacks i=base.stacks i
  registerFrame : ∀i : Fin 40,16 ≤ i.val → i.val < 24 → out.regs i=base.regs i
  lowBlank : ∀i : Fin 768,i.val < 190 → base.stacks i=[] → out.stacks i=[]

 theorem ArithmeticOutput.protected_frame {base out : Data} {m : Circuit.Model}
    {hd : 0 < m.val 34} {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {u : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (h : ArithmeticOutput base out m hd M cache u e)
    (i : Fin 768) (hi : Protected i) : out.stacks i=base.stacks i := by
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hi
  · exact h.collectorFrame _ (by decide) (by decide)
  · exact h.collectorFrame _ (by decide) (by decide)
  · exact h.collectorFrame _ (by decide) (by decide)
  · exact h.highFrame _ (by decide) (by decide) (by decide)
  · exact h.highFrame _ (by decide) (by decide) (by decide)
  · exact h.highFrame _ (by decide) (by decide) (by decide)
  · exact h.highFrame _ (by decide) (by decide) (by decide)
  · exact h.highFrame _ (by decide) (by decide) (by decide)
  · apply h.highFrame i (by omega)
    · intro he
      have hh : i.val=699 := congrArg Fin.val he
      omega
    · intro he
      have hh : i.val < 744 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      omega

 theorem arithmetic_eval (base : Data) (m : Circuit.Model)
    (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks base)=Bank.state r w)
    (W V L : ℕ) (hinit : ∀i,(base.stacks i).length ≤ W)
    (hv : ∀i,(Circuit.result Serialization.code m).val i ≤ V)
    (hw : ∀i,(Circuit.result Serialization.code m).len i ≤ L)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44=3^(m.val 34)-2)
    (h728 : base.stacks 728=[]) :
    ∃ n ≤ arithmeticBudget m W V L (base.stacks 740).length,
      ∃ (e : LeafRingSetupProgram.Data)
        (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
        (cache : RingProgram.ScalarCache 3 (m.val 33))
        (u : RingProgram.ScalarCode 3 (m.val 33)) (out : Data),
      Eval arithmetic n base out ∧ ArithmeticOutput base out m hd M cache u e ∧
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
        (LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd)
          M cache u (base.stacks 740).length) *
        (2 : (IrreducibleSearch.data hd).O (m.val 33)) ^ ((base.stacks 740).length-1)=1 := by
  obtain ⟨nr,hnr,e,M,cache,u,b,hr,hp,hlow,h713,h714,h715,h716,h717,hprivate,hhigh,hcollector,hregs,hlowBlank⟩ :=
    Ring.command_eval base m w r hs ha W V L hinit hv hw ht hd hexp
  have hf728 : b.stacks 728=base.stacks 728 := hhigh _ (by decide) (by decide) (by decide)
  have hf740 : b.stacks 740=base.stacks 740 := hhigh _ (by decide) (by decide) (by decide)
  have hbwidth : ∀i,(b.stacks i).length ≤ W+Ring.budget m W V L+1 := by
    intro i
    have hi := LeafRingSetupProgram.Interpolation.eval_width hr hinit i
    omega
  obtain ⟨nd,hnd,out,he,hout,hinv,hdregs⟩ :=
    LayoutDenominatorProgramQuery.produced_command_eval b m ht hd M cache u e hp hlow
      (fun i hi hj => hprivate i hi (by omega)) (hf728.trans h728) _ hbwidth
  have frame (i : Fin 768) (hi : i≠728) : out.stacks i=b.stacks i := by
    rw [hout,Function.update_of_ne hi]
  have hv728 : out.stacks 728=RingProgram.flat (LayoutDenominatorProgramQuery.value
      (m.val 33) (IrreducibleSearch.data hd) M cache u (base.stacks 740).length) := by
    simp only [hout,Function.update_same,hf740]
  refine ⟨nr+nd,?_,e,M,cache,u,out,hr.seq he,?_,?_⟩
  · rw [hf740] at hnd
    unfold arithmeticBudget
    omega
  · refine ⟨hp,?_,(frame _ (by decide)).trans h713,(frame _ (by decide)).trans h714,
      (frame _ (by decide)).trans h715,(frame _ (by decide)).trans h716,
      (frame _ (by decide)).trans h717,hv728,?_,?_,?_,?_,?_⟩
    · intro i hi
      apply Eq.trans (frame _ ?_) (hlow i hi)
      intro h
      have hh := congrArg Fin.val h
      dsimp [LeafRingSetupProgram.wideStacks] at hh
      omega
    · intro i hi hj
      apply Eq.trans (frame i ?_) (hprivate i hi hj)
      intro h
      have hh : i.val=728 := congrArg Fin.val h
      omega
    · intro i hi h699 ho
      have h728' : i≠728 := by intro h; subst i; simp at ho
      rw [frame i h728']
      apply hhigh i hi h699
      intro hh
      apply ho
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hh ⊢
      rcases hh with hh|hh|hh|hh|hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inl hh))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hh)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hh))))
    · intro i hi hj
      apply Eq.trans (frame i ?_) (hcollector i hi hj)
      intro h
      have hh : i.val=728 := congrArg Fin.val h
      omega
    · intro i hi hj
      exact (hdregs i hi).trans (hregs i hi hj)
    · intro i hi hz
      apply Eq.trans (frame i ?_) (hlowBlank i hi hz)
      intro h
      have hh : i.val=728 := congrArg Fin.val h
      omega
  · simpa only [hf740] using hinv

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
