import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramFinish

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def portIndex (d : Data) (pairs : List (Bool × Bool)) : ℕ :=
  BinaryArithmetic.toNat (Shift.result (d.regs 12) pairs)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14)

def portAccum (d : Data) (a b : Bool) (pairs : List (Bool × Bool)) : List Bool :=
  if portIndex d pairs < BinaryArithmetic.toNat (d.stacks 4) then
    (SubexpLiftRing.fixedBits (d.stacks 5).length
      (portIndex d pairs+coefficientValue a b (BinaryArithmetic.toNat (d.stacks 4)))).reverse++d.stacks 13
  else d.stacks 13

def portStacks (d : Data) (qt st acc : List Bool) : Fin 64 → List Bool :=
  Function.update (Function.update (Function.update (Function.update d.stacks 0 qt) 1 st)
    13 acc) 14 (CounterPrograms.ripple true (d.stacks 14))

theorem portStep_eval (d : Data) (a b : Bool) (qt st : List Bool)
    (pairs : List (Bool × Bool))
    (hq : d.stacks 0=Cell.frame a b++qt)
    (hs : d.stacks 1=Shift.frames (pairs.map Prod.snd)++st)
    (hv : d.stacks 2=pairs.map Prod.fst)
    (h17 : d.stacks 17=[]) (h18 : d.stacks 18=[]) (h19 : d.stacks 19=[])
    (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[])
    (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[]) (h41 : d.stacks 41=[])
    (ha : ∀ i, d.stacks (arithmeticWork i)=[])
    (hc : ∀ i : Fin 8, 2 ≤ i.val → d.stacks (compareStacks i)=[])
    (hcap : 3*BinaryArithmetic.toNat (d.stacks 4) ≤ 2^(d.stacks 5).length) :
    ∃ n rf, Eval portStep n d ⟨rf,portStacks d qt st (portAccum d a b pairs)⟩ ∧
      n ≤ 2000*(portWidth d+1)^2 ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=coefficientRegs d.regs a b i) := by
  obtain ⟨np,rp,prod,idx,ep,vp,flagp,lp,li,bp,fp⟩ :=
    preparePort_eval d a b qt st pairs hq hs hv h17 h18 h19 h20 h21 h24 ha hc
  let p : Data := ⟨rp,preparedStacks d qt st (Shift.result (d.regs 12) pairs) prod idx⟩
  have p8 : p.regs 8=a := by simpa [p,coefficientRegs] using fp 8 (by decide)
  have p9 : p.regs 9=b := by simpa [p,coefficientRegs] using fp 9 (by decide)
  have po : BinaryArithmetic.toNat (offsetWord p)=coefficientValue a b (BinaryArithmetic.toNat (d.stacks 4)) := by
    rw [offsetWord_value_bits,p8,p9]
    simp [p,preparedStacks]
  have pv : BinaryArithmetic.toNat idx=portIndex d pairs := vp
  have pflag : p.regs 7=true ↔ portIndex d pairs < BinaryArithmetic.toNat (d.stacks 4) := by
    simpa [p,pv] using flagp
  have pha : ∀ i, p.stacks (arithmeticWork i)=[] := by
    intro i
    have h := ha i
    have h0 : arithmeticWork i ≠ (0 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 0 at hv
      omega
    have h1 : arithmeticWork i ≠ (1 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 1 at hv
      omega
    have h18 : arithmeticWork i ≠ (18 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 18 at hv
      omega
    have h20 : arithmeticWork i ≠ (20 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 20 at hv
      omega
    have h21 : arithmeticWork i ≠ (21 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 21 at hv
      omega
    simpa [p, preparedStacks, h0, h1, h18, h20, h21] using h
  have pcap : p.regs 7=true → BinaryArithmetic.toNat (p.stacks 21)+BinaryArithmetic.toNat (offsetWord p) < 2^(p.stacks 5).length := by
    intro hg
    have hlt := pflag.mp hg
    have hco := coefficientValue_le a b (BinaryArithmetic.toNat (d.stacks 4))
    change BinaryArithmetic.toNat idx+BinaryArithmetic.toNat (offsetWord p) < 2^(d.stacks 5).length
    rw [pv,po]
    exact lt_of_lt_of_le (by omega :
      portIndex d pairs+coefficientValue a b (BinaryArithmetic.toNat (d.stacks 4)) < 3*BinaryArithmetic.toNat (d.stacks 4)) hcap
  obtain ⟨nf,rf,ef,bf,ff⟩ := finishPort_eval p
    (by simpa [p,preparedStacks] using h22) (by simpa [p,preparedStacks] using h23)
    (by simpa [p,preparedStacks] using h24) (by simpa [p,preparedStacks] using h25)
    (by simpa [p,preparedStacks] using h41) pha pcap
  have pe : emitted p=portAccum d a b pairs := by
    simp only [emitted,portAccum,pflag,po]
    change (if portIndex d pairs < BinaryArithmetic.toNat (d.stacks 4) then
      (SubexpLiftRing.fixedBits (d.stacks 5).length
        (BinaryArithmetic.toNat idx+coefficientValue a b (BinaryArithmetic.toNat (d.stacks 4)))).reverse++d.stacks 13
      else d.stacks 13) = _
    rw [pv]
  have pout : finishedStacks p=portStacks d qt st (portAccum d a b pairs) := by
    funext i
    by_cases h0i : i=0
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks]
    by_cases h1i : i=1
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks]
    by_cases h13i : i=13
    · subst i
      change emitted p=portAccum d a b pairs
      exact pe
    by_cases h14i : i=14
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks]
    by_cases h18i : i=18
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks,h18]
    by_cases h20i : i=20
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks,h20]
    by_cases h21i : i=21
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks,h21]
    simp [finishedStacks,portStacks,p,preparedStacks,
      h0i,h1i,h13i,h14i,h18i,h20i,h21i]
  refine ⟨np+nf,rf,?_,?_,?_⟩
  · simpa only [pout] using ep.seq ef
  · have h4 : (p.stacks 4).length ≤ portWidth d := by simp [p,preparedStacks,portWidth] ; omega
    have h5 : (p.stacks 5).length ≤ portWidth d := by simp [p,preparedStacks,portWidth] ; omega
    have h21p : (p.stacks 21).length ≤ portWidth d := by simpa [p,preparedStacks] using li
    have bap := appendCost_le p (portWidth d) h21p h4 h5
    have hshift : (Shift.result (d.regs 12) pairs).length ≤ portWidth d := by
      have hpairs : pairs.length=(d.stacks 2).length := by rw [hv]; simp
      simp [Shift.result,hpairs,portWidth] ; omega
    have hport : (d.stacks 14).length ≤ portWidth d := by dsimp [portWidth]; omega
    have bfin : nf ≤ 500*(portWidth d+1)^2+14*portWidth d+20 := by
      change nf ≤ appendCost p+2*((Shift.result (d.regs 12) pairs).length+
        prod.length+idx.length)+8*(d.stacks 14).length+20 at bf
      omega
    nlinarith only [bp,bfin,Nat.zero_le (portWidth d)]
  · intro i hi
    exact (ff i hi).trans (fp i hi)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
