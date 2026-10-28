import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramVertexLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramInitialize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramSupplied

namespace OAI.Algorithms

/-! Native serializer endpoint. Runtime bounds are carried in unary tapes;
source arrays and arithmetic operands are copied by the actual table. -/

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def inputState {r D t : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3) : Data :=
  ⟨regs,fun j => if j=3 then dword else if j=4 then mword else if j=5 then width else
    if j=6 then List.replicate D true else if j=7 then List.replicate t true else
    if j=8 then List.replicate (2^r) true else if j=9 then CodeSearchProgram.matrixFrames shifts else
    if j=10 then CodeSearchProgram.matrixFrames Q else if j=11 then List.replicate r true else []⟩

def outputState {r D t m : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3) : Data :=
  ⟨regs,Function.update (Function.update (inputState regs dword mword width shifts Q).stacks 8 [])
    12 (rowStream width.length m shifts Q)⟩

def cost {r D t : ℕ} (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3) : ℕ :=
  let d := inputState (fun _ => false) dword mword width shifts Q
  2^r*(vertexCost ⟨d.regs,initialStacks d⟩ D t width.length+2)+13*r+18

theorem command_eval {r D t m : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (hd : BinaryArithmetic.toNat dword=D) (hm : BinaryArithmetic.toNat mword=m) (hcap : 3*m ≤ 2^width.length) :
    ∃ n rf, Eval command n (inputState regs dword mword width shifts Q)
      (outputState (m:=m) rf dword mword width shifts Q) ∧
      n+1 ≤ cost dword mword width shifts Q := by
  let d := inputState regs dword mword width shifts Q
  obtain ⟨ri,hi⟩ := initialize_eval d (by simp [d,inputState]) (by simp [d,inputState])
    (by simp [d,inputState]) (by simp [d,inputState]) (by simp [d,inputState])
  let start : Data := ⟨ri,initialStacks d⟩
  have ready : LocalReady start D m width.length (start.regs 12) (0 : Cayley.Cube r) := by
    constructor
    · rfl
    · simp [start,initialStacks,d,inputState,vertexBits]
    · simpa [start,initialStacks,d,inputState] using hd
    · simpa [start,initialStacks,d,inputState] using hm
    · simp [start,initialStacks,d,inputState]
    · exact hcap
    · intro j hj hk
      have hne (k : Fin 64) (hlt : k.val < 17) : j ≠ k := by
        intro h
        have hv := congrArg Fin.val h
        omega
      simp only [start,initialStacks,d,inputState,
        Function.update_of_ne (hne 2 (by decide)),
        Function.update_of_ne (hne 12 (by decide)),
        ite_eq_right (hne 3 (by decide)),ite_eq_right (hne 4 (by decide)),
        ite_eq_right (hne 5 (by decide)),ite_eq_right (hne 6 (by decide)),
        ite_eq_right (hne 7 (by decide)),ite_eq_right (hne 8 (by decide)),
        ite_eq_right (hne 9 (by decide)),ite_eq_right (hne 10 (by decide)),
        ite_eq_right (hne 11 (by decide))]
  obtain ⟨nl,e,hl,inv,he8,hnl⟩ := vertexLoop_eval start shifts Q width.length ready
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState,matrixFrames_shifts])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
    (by simp [start,initialStacks,d,inputState])
  have clear := clear_eval 2 e
  have e12 : e.stacks 12=rowStream width.length m shifts Q := by
    simpa [vertexPrefix_full,start,initialStacks,d,inputState,collectedRows_encodeList,
      rowStream,serializedRows] using inv.output
  have out : cleared 2 e=outputState (m:=m) (cleared 2 e).regs dword mword width shifts Q := by
    apply CounterForPrograms.data_ext (a := cleared 2 e)
      (b := outputState (m:=m) (cleared 2 e).regs dword mword width shifts Q)
    · rfl
    · funext j
      by_cases h2 : j=2
      · subst j; simp [cleared,outputState,inputState]
      by_cases h8 : j=8
      · subst j; simp [cleared,outputState,he8]
      by_cases h12 : j=12
      · subst j; simp [cleared,outputState,e12]
      have hj := inv.other j h2 h8 h12
      simpa [cleared,outputState,start,initialStacks,d,inputState,h2,h8,h12] using hj
  refine ⟨(11*(d.stacks 11).length+10)+(nl+(2*(e.stacks 2).length+3)),
    (cleared 2 e).regs,?_,?_⟩
  · rw [←out]
    exact hi.seq (hl.seq clear)
  · have hlen := inv.length
    have costeq : vertexCost start D t width.length=
        vertexCost ⟨(inputState (fun _ => false) dword mword width shifts Q).regs,
          initialStacks (inputState (fun _ => false) dword mword width shifts Q)⟩ D t width.length := rfl
    rw [costeq] at hnl
    have hdlen : (d.stacks 11).length=r := by simp [d,inputState]
    simp only [hdlen]
    dsimp only [cost]
    omega

theorem program_runsIn {r D t m : ℕ} (regs : Fin 16 → Bool) (dword mword width : List Bool)
    (shifts : Fin D → Cayley.Cube r) (Q : Fin t → Fin D → SparseCode.F3)
    (hd : BinaryArithmetic.toNat dword=D) (hm : BinaryArithmetic.toNat mword=m) (hcap : 3*m ≤ 2^width.length) :
    ∃ rf, RunsIn program (cost dword mword width shifts Q)
      ((inputState regs dword mword width shifts Q).withPC (some program.entry))
      ((outputState (m:=m) rf dword mword width shifts Q).withPC none) := by
  obtain ⟨n,rf,he,hn⟩ := command_eval regs dword mword width shifts Q hd hm hcap
  exact ⟨rf,n+1,hn,compiled_halt_trace he 10 12⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
