import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCheckLoop

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def sideCost (d : Data) (D t b : ℕ) : ℕ :=
  7*(d.stacks 10).length+7*(d.stacks 7).length+t*(rowCost d D b+2)+13

theorem sideStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (b : ℕ) (ready : LocalReady base D m b (base.regs 12) v)
    (hq : base.stacks 10=CodeSearchProgram.matrixFrames Q)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D) (ht : (base.stacks 7).length=t)
    (h0 : base.stacks 0=[]) (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) (h16 : base.stacks 16=[]) :
    ∃ n rf, Eval (sideStep side) n base
      ⟨rf,Function.update base.stacks 12
        (collectedRows b (checkRows m shifts Q side v) (base.stacks 12))⟩ ∧
      n ≤ sideCost base D t b ∧ (∀ j : Fin 16, 13 ≤ j.val → rf j=base.regs j) := by
  let d0 : Data := ⟨Function.update base.regs 12 side,base.stacks⟩
  let d1 := copied 10 0 d0
  let d2 := copied 7 16 d1
  have set : Eval (.base (.atom (.set 12 side))) 1 base d0 := .base (.atom _ _)
  have c1 := copy_eval 10 0 d0 (by decide) (by decide) (by decide)
    (ready.work 24 (by decide) (by decide))
  have c2 := copy_eval 7 16 d1 (by decide) (by decide) (by decide)
    (by simpa [d1,d0,copied,copyStacks] using ready.work 24 (by decide) (by decide))
  have rd : LocalReady d2 D m b side v := by
    constructor
    · simp [d2,d1,d0,copied,readRegs]
    · simpa [d2,d1,d0,copied,copyStacks] using ready.vertex
    · simpa [d2,d1,d0,copied,copyStacks] using ready.degree
    · simpa [d2,d1,d0,copied,copyStacks] using ready.modulus
    · simpa [d2,d1,d0,copied,copyStacks] using ready.width
    · exact ready.capacity
    · intro j hj hk
      have hj0 : j≠0 := by intro hne; have hv := congrArg Fin.val hne; change j.val=0 at hv; omega
      have hj16 : j≠16 := by intro hne; have hv := congrArg Fin.val hne; change j.val=16 at hv; omega
      simpa [d2,d1,d0,copied,copyStacks,hj0,hj16] using ready.work j hj hk
  obtain ⟨nl,e,hl,inv,he16,hnl⟩ := checkLoop_eval d2 shifts Q side v b rd
    (by simp [d2,d1,d0,copied,copyStacks,h0,hq,matrixSuffix,matrixFrames_rows])
    (by simpa [d2,d1,d0,copied,copyStacks] using hs)
    (by simpa [d2,d1,d0,copied,copyStacks] using hD)
    (by simpa [d2,d1,d0,copied,copyStacks] using h1)
    (by simpa [d2,d1,d0,copied,copyStacks] using h13)
    (by simpa [d2,d1,d0,copied,copyStacks] using h14)
    (by simpa [d2,d1,d0,copied,copyStacks] using h15)
    (by simpa [d2,d1,d0,copied,copyStacks,h16] using ht)
  have hdrop : (List.ofFn fun a => CodeSearchProgram.scalarFrames (List.ofFn (Q a))).drop t = [] := by
    apply List.drop_eq_nil_of_le
    simp
  have e0 : e.stacks 0=[] := by simpa only [matrixSuffix,hdrop,List.flatten_nil] using inv.source
  have htake : (checkRows m shifts Q side v).take t = checkRows m shifts Q side v := by
    apply List.take_of_length_le
    simp [checkRows]
  have e12 : e.stacks 12=collectedRows b (checkRows m shifts Q side v) (base.stacks 12) := by
    simpa only [htake,d2,d1,d0,copied,copyStacks,
      Function.update_of_ne (by decide : (12 : Fin 64) ≠ 16),
      Function.update_of_ne (by decide : (12 : Fin 64) ≠ 0)] using inv.output
  have hout : e.stacks=Function.update base.stacks 12
      (collectedRows b (checkRows m shifts Q side v) (base.stacks 12)) := by
    funext j
    by_cases hj0 : j=0
    · subst j; simp [e0,h0]
    by_cases hj12 : j=12
    · subst j; simp [e12]
    by_cases hj16 : j=16
    · subst j; simp [he16,h16]
    simpa [d2,d1,d0,copied,copyStacks,hj0,hj12,hj16] using inv.other j hj0 hj12 hj16
  have e_eq : e=(⟨e.regs,Function.update base.stacks 12
      (collectedRows b (checkRows m shifts Q side v) (base.stacks 12))⟩ : Data) := by
    cases e; simp_all
  have costeq : rowCost d2 D b=rowCost base D b := by
    simp [rowCost,portWidth,d2,d1,d0,copied,copyStacks]
  refine ⟨1+((7*(d0.stacks 10).length+5)+((7*(d1.stacks 7).length+5)+nl)),
    e.regs,?_,?_,?_⟩
  · rw [←e_eq]
    exact set.seq (c1.seq (c2.seq hl))
  · simp only [d1,d0,copied,copyStacks,
      Function.update_noteq (by decide : (7 : Fin 64)≠0)]
    rw [costeq] at hnl
    unfold sideCost
    omega
  · intro j hj
    rw [inv.registers j (by omega),copied_register 7 16 d1 j (by omega),
      copied_register 10 0 d0 j (by omega)]
    have hj12 : j≠12 := by intro hne; have hv := congrArg Fin.val hne; change j.val=12 at hv; omega
    simp [d0,hj12]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
