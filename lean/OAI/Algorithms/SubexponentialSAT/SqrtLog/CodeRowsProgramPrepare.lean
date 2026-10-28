import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramRead
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramShiftCall
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCompareCall

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def portWidth (d : Data) : ℕ :=
  (d.stacks 2).length+(d.stacks 3).length+(d.stacks 4).length+
    (d.stacks 5).length+(d.stacks 14).length+3

def preparedStacks (d : Data) (qt st shifted product idx : List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update
    (Function.update (Function.update (Function.update d.stacks 0 qt) 1 st) 18 shifted)
      20 product) 21 idx

theorem preparePort_eval (d : Data) (a b : Bool) (qt st : List Bool)
    (pairs : List (Bool × Bool))
    (hq : d.stacks 0=Cell.frame a b++qt)
    (hs : d.stacks 1=Shift.frames (pairs.map Prod.snd)++st)
    (hv : d.stacks 2=pairs.map Prod.fst)
    (h17 : d.stacks 17=[]) (h18 : d.stacks 18=[]) (h19 : d.stacks 19=[])
    (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[]) (h24 : d.stacks 24=[])
    (ha : ∀ i, d.stacks (arithmeticWork i)=[])
    (hc : ∀ i : Fin 8, 2 ≤ i.val → d.stacks (compareStacks i)=[]) :
    ∃ n rf product idx, Eval preparePort n d
      ⟨rf,preparedStacks d qt st (Shift.result (d.regs 12) pairs) product idx⟩ ∧
      BinaryArithmetic.toNat idx=BinaryArithmetic.toNat (Shift.result (d.regs 12) pairs)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14) ∧
      (rf 7=true ↔ BinaryArithmetic.toNat idx < BinaryArithmetic.toNat (d.stacks 4)) ∧
      product.length ≤ portWidth d ∧ idx.length ≤ portWidth d ∧
      n ≤ 600*(portWidth d)^2 ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=coefficientRegs d.regs a b i) := by
  have e0 := readCoefficient_eval d a b qt hq
  let d0 : Data := ⟨coefficientRegs d.regs a b,Function.update d.stacks 0 qt⟩
  obtain ⟨r1,e1,f1⟩ := shiftVertex_eval d0 pairs st
    (by simpa [d0] using hs) (by simpa [d0] using hv)
    (by simpa [d0] using h17) (by simpa [d0] using h18)
    (by simpa [d0] using h19) (by simpa [d0] using h24)
  have hm : d0.regs 12=d.regs 12 := by simp [d0,coefficientRegs]
  rw [hm] at e1
  let shifted := Shift.result (d.regs 12) pairs
  let d1 : Data := ⟨r1,Function.update (Function.update d0.stacks 1 st) 18 shifted⟩
  have ha1 : ∀ i, d1.stacks (arithmeticWork i)=[] := by
    intro i
    have h := ha i
    have hi0 : arithmeticWork i ≠ (0 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 0 at hv
      omega
    have hi1 : arithmeticWork i ≠ (1 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 1 at hv
      omega
    have hi18 : arithmeticWork i ≠ (18 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 18 at hv
      omega
    simpa [d1, d0, hi0, hi1, hi18] using h
  obtain ⟨n2,r2,product,idx,e2,v2,lprod,lidx,b2,f2⟩ := index_eval d1
    (by simpa [d1,d0] using h20) (by simpa [d1,d0] using h21) ha1
  let d2 : Data := ⟨r2,Function.update (Function.update d1.stacks 20 product) 21 idx⟩
  have hc2 : ∀ i : Fin 8, 2 ≤ i.val → d2.stacks (compareStacks i)=[] := by
    intro i hi
    have h := hc i hi
    fin_cases i <;> simp_all [d2,d1,d0,compareStacks]
  obtain ⟨r3,e3,flag3,f3⟩ := belowClauseCount_eval d2 hc2
  have hpairs : pairs.length=(d.stacks 2).length := by rw [hv]; simp
  have hiwidth : indexWidth (projectState low8 id d1) ≤ portWidth d := by
    simp [indexWidth,projectState,d1,d0,shifted,Shift.result,portWidth,hpairs] ; omega
  have hprod : product.length ≤ portWidth d := lprod.trans hiwidth
  have hidx : idx.length ≤ portWidth d := lidx.trans hiwidth
  have hnv : n2 ≤ 200*(portWidth d)^2+1 := by
    apply b2.trans
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hiwidth 2)) _
  let n := 6+(21*pairs.length+12+(n2+
    (52*((d2.stacks 21).length+(d2.stacks 4).length)+54)))
  refine ⟨n,r3,product,idx,e0.seq (e1.seq (e2.seq e3)),?_,?_,hprod,hidx,?_,?_⟩
  · simpa [d1,d0,shifted] using v2
  · simpa [d2,d1,d0] using flag3
  · have hW : 3 ≤ portWidth d := by dsimp [portWidth]; omega
    have hpW : pairs.length ≤ portWidth d := by rw [hpairs]; dsimp [portWidth]; omega
    have hmW : (d.stacks 4).length ≤ portWidth d := by dsimp [portWidth]; omega
    dsimp [n]
    simp only [d2,d1,d0,Function.update_same,
      Function.update_noteq (by decide : (4 : Fin 64)≠21),
      Function.update_noteq (by decide : (4 : Fin 64)≠20),
      Function.update_noteq (by decide : (4 : Fin 64)≠18),
      Function.update_noteq (by decide : (4 : Fin 64)≠1),
      Function.update_noteq (by decide : (4 : Fin 64)≠0)]
    nlinarith only [hW,hpW,hmW,hnv,hidx]
  · intro i hi
    exact (f3 i hi).trans ((f2 i hi).trans (f1 i hi))

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
