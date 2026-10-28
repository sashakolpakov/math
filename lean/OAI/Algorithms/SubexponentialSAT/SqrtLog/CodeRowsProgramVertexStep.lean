import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSide

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def vertexRows {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (v : Cayley.Cube r) :
    List (List (Fin m × SparseCode.F3)) :=
  checkRows m shifts Q false v++checkRows m shifts Q true v

def vertexCost (d : Data) (D t b : ℕ) : ℕ := 2*sideCost d D t b+8*(d.stacks 2).length+8

theorem vertexStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (v : Cayley.Cube r)
    (b : ℕ) (ready : LocalReady base D m b (base.regs 12) v)
    (hq : base.stacks 10=CodeSearchProgram.matrixFrames Q)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D) (ht : (base.stacks 7).length=t)
    (h0 : base.stacks 0=[]) (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) (h16 : base.stacks 16=[]) :
    ∃ n rf, Eval vertexStep n base
      ⟨rf,Function.update (Function.update base.stacks 12
        (collectedRows b (vertexRows m shifts Q v) (base.stacks 12))) 2
          (CounterPrograms.ripple true (base.stacks 2))⟩ ∧
      n ≤ vertexCost base D t b ∧ (∀ j : Fin 16, 13 ≤ j.val → rf j=base.regs j) := by
  obtain ⟨nl,rl,hl,hnl,hrl⟩ := sideStep_eval base shifts Q false v b ready hq hs hD ht
    h0 h1 h13 h14 h15 h16
  let d1 : Data := ⟨rl,Function.update base.stacks 12
    (collectedRows b (checkRows m shifts Q false v) (base.stacks 12))⟩
  have rd : LocalReady d1 D m b (d1.regs 12) v := by
    constructor
    · rfl
    · simpa [d1] using ready.vertex
    · simpa [d1] using ready.degree
    · simpa [d1] using ready.modulus
    · simpa [d1] using ready.width
    · exact ready.capacity
    · intro j hj hk
      have hj12 : j≠12 := by intro hne; have hv := congrArg Fin.val hne; change j.val=12 at hv; omega
      simpa [d1,hj12] using ready.work j hj hk
  obtain ⟨nr,rr,hr,hnr,hrr⟩ := sideStep_eval d1 shifts Q true v b rd
    (by simpa [d1] using hq) (by simpa [d1] using hs)
    (by simpa [d1] using hD) (by simpa [d1] using ht)
    (by simpa [d1] using h0) (by simpa [d1] using h1)
    (by simpa [d1] using h13) (by simpa [d1] using h14)
    (by simpa [d1] using h15) (by simpa [d1] using h16)
  let d2 : Data := ⟨rr,Function.update d1.stacks 12
    (collectedRows b (checkRows m shifts Q true v) (d1.stacks 12))⟩
  have h41 : d2.stacks 41=[] := by simpa [d2,d1] using ready.work 41 (by decide) (by decide)
  have inc := increment_eval d2 2 (by decide) h41
  have out : (incremented d2 2 (by decide)).stacks=
      Function.update (Function.update base.stacks 12
        (collectedRows b (vertexRows m shifts Q v) (base.stacks 12))) 2
          (CounterPrograms.ripple true (base.stacks 2)) := by
    rw [incremented_stacks d2 2 (by decide) h41]
    simp [d2,d1,vertexRows,collectedRows_append]
  have final : incremented d2 2 (by decide)=
      (⟨(incremented d2 2 (by decide)).regs,
      Function.update (Function.update base.stacks 12
        (collectedRows b (vertexRows m shifts Q v) (base.stacks 12))) 2
          (CounterPrograms.ripple true (base.stacks 2))⟩ : Data) := by
    exact CounterForPrograms.data_ext (a := incremented d2 2 (by decide)) rfl out
  refine ⟨nl+(nr+(CounterPrograms.rippleCost true (d2.stacks 2)+1)),
    (incremented d2 2 (by decide)).regs,?_,?_,?_⟩
  · rw [←final]
    exact hl.seq (hr.seq inc)
  · have hinc := CounterPrograms.rippleCost_le true (d2.stacks 2)
    have same : sideCost d1 D t b=sideCost base D t b := by
      simp [sideCost,rowCost,portWidth,d1]
    rw [same] at hnr
    simp only [d2,d1,Function.update_noteq (by decide : (2 : Fin 64)≠12)] at hinc ⊢
    unfold vertexCost
    omega
  · intro j hj
    rw [incremented_register d2 2 (by decide) j (by omega)]
    exact (hrr j hj).trans (hrl j hj)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
