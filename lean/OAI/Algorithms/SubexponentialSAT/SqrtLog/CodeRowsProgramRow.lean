import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramLocal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramWrite

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.StackRoutines

def rowCost (d : Data) (D b : ℕ) : ℕ :=
  7*(d.stacks 6).length+7*(d.stacks 9).length+
    D*(2000*(portWidth d+D+1)^2+2)+2*D+4*(D*b)+23

def rowStacks (d : Data) (qt payload : List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update d.stacks 0 qt) 12
    (true::(Encoding.frame payload++d.stacks 12))

theorem rowStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt : List Bool) (ready : LocalReady base D m b side v)
    (hq : base.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++qt)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D)
    (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) :
    ∃ n rf, Eval rowStep n base
      ⟨rf,rowStacks base qt (rowPayload b m (slots m shifts Q side v a))⟩ ∧
      n ≤ rowCost base D b ∧ (∀ j : Fin 16, 12 ≤ j.val → rf j=base.regs j) := by
  let d1 := copied 6 15 base
  let d2 := copied 9 1 d1
  have c1 := copy_eval 6 15 base (by decide) (by decide) (by decide)
    (ready.work 24 (by decide) (by decide))
  have c2 := copy_eval 9 1 d1 (by decide) (by decide) (by decide)
    (by simpa [d1,copied,copyStacks] using ready.work 24 (by decide) (by decide))
  have rd : LocalReady d2 D m b side v := by
    constructor
    · simpa [d2,d1,copied,readRegs] using ready.mode
    · simpa [d2,d1,copied,copyStacks] using ready.vertex
    · simpa [d2,d1,copied,copyStacks] using ready.degree
    · simpa [d2,d1,copied,copyStacks] using ready.modulus
    · simpa [d2,d1,copied,copyStacks] using ready.width
    · exact ready.capacity
    · intro j hj hk
      have hj1 : j≠1 := by intro hne; have hv := congrArg Fin.val hne; change j.val=1 at hv; omega
      have hj15 : j≠15 := by intro hne; have hv := congrArg Fin.val hne; change j.val=15 at hv; omega
      simpa [d2,d1,copied,copyStacks,hj1,hj15] using ready.work j hj hk
  obtain ⟨nl,e,hl,inv,he15,hnl⟩ := localLoop_eval d2 shifts Q side v a b qt [] rd
    (by simpa [d2,d1,copied,copyStacks] using hq)
    (by simp [d2,d1,copied,copyStacks,h1,hs])
    (by simpa [d2,d1,copied,copyStacks] using h14)
    (by simpa [d2,d1,copied,copyStacks,h15] using hD)
  let d3 := cleared 14 e
  have cl := clear_eval 14 e
  obtain ⟨rf,hw,hr⟩ := writeRow_eval d3
  have hqdrop : (List.ofFn (Q a)).drop D = [] := by
    apply List.drop_eq_nil_of_le
    simp
  have hsdrop : (List.ofFn shifts).drop D = [] := by
    apply List.drop_eq_nil_of_le
    simp
  have e0 : e.stacks 0=qt := by
    simpa [hqdrop, CodeSearchProgram.scalarFrames, Subexp.MatrixProgramSupport.words]
      using inv.source
  have e1 : e.stacks 1=[] := by simpa [hsdrop,shiftRows] using inv.shiftSource
  have e13 : e.stacks 13=(rowPayload b m (slots m shifts Q side v a)).reverse := by
    simpa [d2,d1,copied,copyStacks,h13] using inv.accum
  have eother (j : Fin 64) (hj0 : j≠0) (hj1 : j≠1) (hj13 : j≠13)
      (hj14 : j≠14) (hj15 : j≠15) : e.stacks j=base.stacks j := by
    simpa [d2,d1,copied,copyStacks,hj1,hj15] using inv.other j hj0 hj1 hj13 hj14 hj15
  have e12 : e.stacks 12=base.stacks 12 := eother 12 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hout : Function.update (Function.update d3.stacks 13 []) 12
      (true::(Encoding.frame (d3.stacks 13).reverse++d3.stacks 12))=
      rowStacks base qt (rowPayload b m (slots m shifts Q side v a)) := by
    funext j
    by_cases hj0 : j=0
    · subst j; simp [d3,cleared,rowStacks,e0]
    by_cases hj1 : j=1
    · subst j; simp [d3,cleared,rowStacks,e1,h1]
    by_cases hj12 : j=12
    · subst j; simp [d3,cleared,rowStacks,e13,e12]
    by_cases hj13 : j=13
    · subst j; simp [d3,cleared,rowStacks,h13]
    by_cases hj14 : j=14
    · subst j; simp [d3,cleared,rowStacks,h14]
    by_cases hj15 : j=15
    · subst j; simp [d3,cleared,rowStacks,he15,h15]
    simp [d3,cleared,rowStacks,hj0,hj12,hj13,hj14,
      eother j hj0 hj1 hj13 hj14 hj15]
  have width : portWidth d2=portWidth base := by simp [portWidth,d2,d1,copied,copyStacks]
  have payloadBound : (rowPayload b m (slots m shifts Q side v a)).length ≤ D*b :=
    sparse_rowPayload_length b shifts Q side v a
  refine ⟨(7*(base.stacks 6).length+5) + ((7*(d1.stacks 9).length+5) +
    (nl + ((2*(e.stacks 14).length+3) + (4*(d3.stacks 13).length+8)))),rf,?_,?_,?_⟩
  · simpa only [rowStep,hout] using c1.seq (c2.seq (hl.seq (cl.seq hw)))
  · have ei := inv.indexLength
    dsimp [d3,cleared] at hw ⊢
    simp only [Function.update_noteq (by decide : (13 : Fin 64)≠14),e13,
      List.length_reverse] at ⊢
    simp only [d1,copied,copyStacks,Function.update_noteq (by decide : (9 : Fin 64)≠15)]
    rw [width] at hnl
    unfold rowCost
    omega
  · intro j hj
    have hr' : rf j=e.regs j := by
      rw [hr j (by omega)]
      exact cleared_register 14 e j (by omega)
    rw [hr',inv.registers j hj,copied_register 9 1 d1 j (by omega),
      copied_register 6 15 base j (by omega)]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
