import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramInvariant

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

structure LocalReady {r : ℕ} (base : Data) (D m b : ℕ) (side : Bool)
    (v : Cayley.Cube r) : Prop where
  mode : base.regs 12=side
  vertex : base.stacks 2=vertexBits v
  degree : BinaryArithmetic.toNat (base.stacks 3)=D
  modulus : BinaryArithmetic.toNat (base.stacks 4)=m
  width : (base.stacks 5).length=b
  capacity : 3*m ≤ 2^b
  work : ∀ j : Fin 64, 17 ≤ j.val → j.val ≤ 41 → base.stacks j=[]

theorem localStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt st : List Bool) (ready : LocalReady base D m b side v)
    (i : ℕ) (hi : i < D) (d : Data) (inv : LocalInvariant (m:=m) base shifts Q side v a b qt st i d) :
    ∃ n e, n ≤ 2000*(portWidth base+D+1)^2 ∧ Eval portStep n d e ∧
      e.stacks portLoop.counter=d.stacks portLoop.counter ∧
      LocalInvariant (m:=m) base shifts Q side v a b qt st (i+1) e := by
  let p : Fin D := ⟨i,hi⟩
  let pairs := vertexPairs v (shifts p)
  let qt1 := CodeSearchProgram.scalarFrames ((List.ofFn (Q a)).drop (i+1))++qt
  let st1 := shiftRows ((List.ofFn shifts).drop (i+1))++st
  have hq : d.stacks 0=Cell.frame (decide (Q a p=1)) (decide (Q a p=2))++qt1 := by
    rw [inv.source,scalar_drop_head (Q a) i hi]
    simp [p,qt1,List.append_assoc]
  have hs : d.stacks 1=Shift.frames (pairs.map Prod.snd)++st1 := by
    rw [inv.shiftSource,shifts_drop_head shifts i hi]
    simp [p,pairs,st1,List.append_assoc]
  have hv : d.stacks 2=pairs.map Prod.fst := by
    rw [inv.other 2 (by decide) (by decide) (by decide) (by decide) (by decide),ready.vertex]
    simp [pairs]
  have work (j : Fin 64) (h17 : 17 ≤ j.val) (h41 : j.val ≤ 41) : d.stacks j=[] := by
    have h0 : j≠0 := by intro hne; have hv := congrArg Fin.val hne; change j.val=0 at hv; omega
    have h1 : j≠1 := by intro hne; have hv := congrArg Fin.val hne; change j.val=1 at hv; omega
    have h13 : j≠13 := by intro hne; have hv := congrArg Fin.val hne; change j.val=13 at hv; omega
    have h14 : j≠14 := by intro hne; have hv := congrArg Fin.val hne; change j.val=14 at hv; omega
    have h15 : j≠15 := by intro hne; have hv := congrArg Fin.val hne; change j.val=15 at hv; omega
    rw [inv.other j h0 h1 h13 h14 h15]
    exact ready.work j h17 h41
  have ha : ∀ j, d.stacks (arithmeticWork j)=[] := by
    intro j
    fin_cases j <;> exact work _ (by decide) (by decide)
  have hc : ∀ j : Fin 8, 2 ≤ j.val → d.stacks (compareStacks j)=[] := by
    intro j hj
    fin_cases j <;> simp_all [compareStacks]
  have hD : BinaryArithmetic.toNat (d.stacks 3)=D := by
    rw [inv.other 3 (by decide) (by decide) (by decide) (by decide) (by decide),ready.degree]
  have hm : BinaryArithmetic.toNat (d.stacks 4)=m := by
    rw [inv.other 4 (by decide) (by decide) (by decide) (by decide) (by decide),ready.modulus]
  have hb : (d.stacks 5).length=b := by
    rw [inv.other 5 (by decide) (by decide) (by decide) (by decide) (by decide),ready.width]
  have hmode : d.regs 12=side := (inv.registers 12 (by decide)).trans ready.mode
  obtain ⟨n,rf,he,hn,hregs⟩ := portStep_eval d (decide (Q a p=1)) (decide (Q a p=2))
    qt1 st1 pairs hq hs hv
    (work 17 (by decide) (by decide)) (work 18 (by decide) (by decide))
    (work 19 (by decide) (by decide)) (work 20 (by decide) (by decide))
    (work 21 (by decide) (by decide)) (work 22 (by decide) (by decide))
    (work 23 (by decide) (by decide)) (work 24 (by decide) (by decide))
    (work 25 (by decide) (by decide)) (work 41 (by decide) (by decide)) ha hc
    (by simpa [hm,hb] using ready.capacity)
  let e : Data := ⟨rf,portStacks d qt1 st1 (portAccum d (decide (Q a p=1)) (decide (Q a p=2)) pairs)⟩
  refine ⟨n,e,?_,he,?_,?_⟩
  · exact hn.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.add_le_add_right inv.width 1) 2))
  · simp [e,portStacks,portLoop]
  · constructor
    · omega
    · intro j hj
      have h0 : j≠0 := by intro hne; have hv := congrArg Fin.val hne; change j.val=0 at hv; omega
      have h1 : j≠1 := by intro hne; have hv := congrArg Fin.val hne; change j.val=1 at hv; omega
      have h8 : j≠8 := by intro hne; have hv := congrArg Fin.val hne; change j.val=8 at hv; omega
      have h9 : j≠9 := by intro hne; have hv := congrArg Fin.val hne; change j.val=9 at hv; omega
      have hr := hregs j (by omega)
      have hr' : rf j=d.regs j := by
        simpa [coefficientRegs,h0,h1,h8,h9] using hr
      change rf j=base.regs j
      exact hr'.trans (inv.registers j hj)
    · simp [e,portStacks,qt1]
    · simp [e,portStacks,st1]
    · have hacc := portAccum_prefix d shifts Q side v a i b hi (base.stacks 13)
        hmode hD hm inv.index hb inv.accum
      simpa [e,portStacks,p,pairs] using hacc
    · have hv' := CounterPrograms.value_increment (d.stacks 14)
      simpa [e,portStacks,CounterPrograms.value_eq_toNat,inv.index] using hv'
    · have hl := CounterPrograms.ripple_length_le true (d.stacks 14)
      have old := inv.indexLength
      simp only [e,portStacks,Function.update_same]
      omega
    · intro j h0 h1 h13 h14 h15
      simpa [e,portStacks,h0,h1,h13,h14] using inv.other j h0 h1 h13 h14 h15

theorem localLoop_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt st : List Bool) (ready : LocalReady base D m b side v)
    (hq : base.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++qt)
    (hs : base.stacks 1=shiftRows (List.ofFn shifts)++st)
    (hp : base.stacks 14=[]) (hcount : (base.stacks 15).length=D) :
    ∃ n e, Eval (UnaryForPrograms.forCmd portLoop portStep) n base e ∧
      LocalInvariant (m:=m) base shifts Q side v a b qt st D e ∧ e.stacks 15=[] ∧
      n ≤ D*(2000*(portWidth base+D+1)^2+2)+2 := by
  apply bounded_for_eval portLoop portStep
    (LocalInvariant (m:=m) base shifts Q side v a b qt st) D (2000*(portWidth base+D+1)^2)
  · intro i d inv; exact inv.popped
  · exact localStep_eval base shifts Q side v a b qt st ready
  · exact hcount
  · exact localInvariant_initial base shifts Q side v a b qt st hq hs hp

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
