import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramMultiplierKeyCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsCanonical
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierArithmetic. -/

/-! Native construction of the cubic multiplier before its U shift. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

/-- A bounded native transition, with all Boolean registers allowed to change. -/
abbrev Runs (command : Cmd 8 96) (cost : ℕ) (low : Fin 56 → List Bool)
    (before after : Data) : Prop :=
  ∀ regs, ∃ k ≤ cost, ∃ rr, Eval command k
    (Memory.state regs low before) (Memory.state rr low after)

theorem Runs.seq {a b : Cmd 8 96} {A B : ℕ} {low} {x y z : Data}
    (ha : Runs a A low x y) (hb : Runs b B low y z) :
    Runs (.seq a b) (A+B) low x z := by
  intro regs
  obtain ⟨i,hi,r1,h1⟩:=ha regs
  obtain ⟨j,hj,r2,h2⟩:=hb r1
  exact ⟨i+j,Nat.add_le_add hi hj,r2,h1.seq h2⟩

theorem Runs.skip (low) (high : Data) : Runs (.base .skip) 0 low high high := by
  intro regs
  exact ⟨0,le_rfl,regs,Eval.base (.skip _)⟩

def work (high : Data) (operand acc saved : List Bool) : Data :=
  Function.update (Function.update (Function.update high 5 operand) 11 acc) 29 saved

@[simp] theorem work_5 (high : Data) (a b c) : work high a b c 5=a := by simp [work]
@[simp] theorem work_11 (high : Data) (a b c) : work high a b c 11=b := by simp [work]
@[simp] theorem work_29 (high : Data) (a b c) : work high a b c 29=c := by simp [work]
@[simp] theorem work_other (high : Data) (a b c) (i : Fin 40)
    (h5:i≠5) (h11:i≠11) (h29:i≠29) : work high a b c i=high i := by
  simp [work,h5,h11,h29]

theorem work_update5 (high : Data) (a b c z) :
    Function.update (work high a b c) 5 z=work high z b c := by
  funext i; by_cases h5:i=5 <;> by_cases h11:i=11 <;> by_cases h29:i=29 <;>
    simp_all [work]
theorem work_update11 (high : Data) (a b c z) :
    Function.update (work high a b c) 11 z=work high a z c := by
  funext i; by_cases h5:i=5 <;> by_cases h11:i=11 <;> by_cases h29:i=29 <;>
    simp_all [work,Function.update_apply]
theorem work_update29 (high : Data) (a b c z) :
    Function.update (work high a b c) 29 z=work high a b z := by simp [work]
theorem work_binary (high : Data) (a b c z) :
    binaryResult (work high a b c) z=work high [] z c := by
  simp only [binaryResult,work_update11,work_update5]
theorem work_empty (high : Data) (h5:high 5=[]) (h11:high 11=[]) (h29:high 29=[]) :
    work high [] [] []=high := by
  funext i; by_cases h5':i=5 <;> by_cases h11':i=11 <;> by_cases h29':i=29 <;>
    simp_all [work]

def complemented (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  Normalize.run p t c.modulus c.cache
    (Squarefree.ScaleProgram.scaled p t c.modulus c.cache c.table minus h) one

def complementCost (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  36*(Product.bytes h).length+18*(RingProgram.flat minus).length+
    7*(Product.bytes one).length+9*(Product.bytes (complemented c minus h one)).length+9*d+
    Squarefree.ScaleProgram.budget Squarefree.encodeIndex h+
    Normalize.work p t c.modulus c.cache Squarefree.encodeIndex
      (Squarefree.ScaleProgram.scaled p t c.modulus c.cache c.table minus h) one+73

def cubic (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  let a:=complemented c minus h one
  mul c (mul c (plus c a one) a) h

abbrev arithmetic : Cmd 8 96 := sequence
  [copy 68 61 70, complement,
   copy 61 85 70, copy 61 67 70, clear 61,
   copy 69 61 70, add,
   copy 85 61 70, productAdapter product, clear 85,
   copy 68 61 70, productAdapter product]

def arithmeticCost (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  let a:=complemented c minus h one
  let b:=plus c a one
  let q:=mul c b a
  (7*(Product.bytes h).length+5)+complementCost c minus h one+
  (7*(Product.bytes a).length+5)+(7*(Product.bytes a).length+5)+
  (2*(Product.bytes a).length+3)+(7*(Product.bytes one).length+5)+addCost c a one+
  (7*(Product.bytes a).length+5)+mulCost c b a+(2*(Product.bytes a).length+3)+
  (7*(Product.bytes h).length+5)+mulCost c q h

/-- All inputs are ordinary stored data. No arithmetic callback premise is used. -/
theorem arithmetic_runs (c : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (high : Data)
    (hh : high 12=Product.bytes h) (ho : high 13=Product.bytes one)
    (hm : high 20=RingProgram.flat minus) (htmp : high 14=[]) :
    Runs arithmetic (arithmeticCost c minus h one) (low c)
      (work high [] [] []) (work high [] (Product.bytes (cubic c minus h one)) []) := by
  let a:=complemented c minus h one
  let b:=plus c a one
  let q:=mul c b a
  let H:=Product.bytes h
  let O:=Product.bytes one
  let A:=Product.bytes a
  let B:=Product.bytes b
  let Q:=Product.bytes q
  let G:=Product.bytes (mul c q h)
  have h61 : (61 : Fin 96) = Memory.highPort 5 := by decide
  have h67 : (67 : Fin 96) = Memory.highPort 11 := by decide
  have h68 : (68 : Fin 96) = Memory.highPort 12 := by decide
  have h69 : (69 : Fin 96) = Memory.highPort 13 := by decide
  have h85 : (85 : Fin 96) = Memory.highPort 29 := by decide
  have hc (src dst : Fin 40) (hsd:src≠dst) (hst:src≠14) (htd:(14:Fin 40)≠dst)
      (x : Data) (hx:x 14=[]) :
      Runs (copy (Memory.highPort src) (Memory.highPort dst) 70)
        (7*(x src).length+5) (low c) x (Function.update x dst (x src++x dst)) := by
    intro regs
    exact ⟨_,le_rfl,_,copy_high_high regs (low c) x src dst 14 hsd hst htd hx⟩
  have he (src : Fin 40) (x : Data) :
      Runs (clear (Memory.highPort src)) (2*(x src).length+3) (low c)
        x (Function.update x src []) := by
    intro regs
    exact ⟨_,le_rfl,_,Memory.clear_high regs (low c) x src⟩
  have h1 : Runs (copy 68 61 70) (7*H.length+5) (low c)
      (work high [] [] []) (work high H [] []) := by
    rw [h68, h61]
    have hh':work high [] [] [] 12=H:=by simpa [work,H] using hh
    simpa only [hh',work_5,List.append_nil,work_update5] using
      hc 12 5 (by decide) (by decide) (by decide) (work high [] [] []) (by simpa [work] using htmp)
  have h2 : Runs complement (complementCost c minus h one) (low c)
      (work high H [] []) (work high A [] []) := by
    intro regs
    have h':=WeightedCallbacks.complement_eval p t c.modulus c.cache c.zeroBound c.table
      minus (List.replicate d true) c.width (List.replicate c.u true) (List.replicate c.J true)
      (by simp) c.widthLength Squarefree.encodeIndex Squarefree.encodeIndex_injective h one regs
      (work high H [] []) (by rfl) (by simpa [work] using hm) (by simpa [work] using ho)
      (by simpa [work] using htmp)
    simpa [low,complementCost,WeightedCallbacks.complementedHigh,work_update5,
      H,A,a,complemented,hm,ho] using h'
  have h3 : Runs (copy 61 85 70) (7*A.length+5) (low c)
      (work high A [] []) (work high A [] A) := by
    rw [h61, h85]
    simpa only [work_5,work_29,List.append_nil,work_update29] using
      hc 5 29 (by decide) (by decide) (by decide) (work high A [] []) (by simpa [work] using htmp)
  have h4 : Runs (copy 61 67 70) (7*A.length+5) (low c)
      (work high A [] A) (work high A A A) := by
    rw [h61, h67]
    simpa only [work_5,work_11,List.append_nil,work_update11] using
      hc 5 11 (by decide) (by decide) (by decide) (work high A [] A) (by simpa [work] using htmp)
  have h5 : Runs (clear 61) (2*A.length+3) (low c)
      (work high A A A) (work high [] A A) := by
    rw [h61]
    simpa only [work_5,work_update5] using he 5 (work high A A A)
  have h6 : Runs (copy 69 61 70) (7*O.length+5) (low c)
      (work high [] A A) (work high O A A) := by
    rw [h69, h61]
    have ho':work high [] A A 13=O:=by simpa [work,O] using ho
    simpa only [ho',work_5,List.append_nil,work_update5] using
      hc 13 5 (by decide) (by decide) (by decide) (work high [] A A) (by simpa [work] using htmp)
  have h7 : Runs add (addCost c a one) (low c)
      (work high O A A) (work high [] B A) := by
    intro regs
    simpa only [work_binary] using Steps.add_eval c a one regs (work high O A A)
      (by rfl) (by rfl) (by simpa [work] using htmp)
  have h8 : Runs (copy 85 61 70) (7*A.length+5) (low c)
      (work high [] B A) (work high A B A) := by
    rw [h85, h61]
    simpa only [work_29,work_5,List.append_nil,work_update5] using
      hc 29 5 (by decide) (by decide) (by decide) (work high [] B A) (by simpa [work] using htmp)
  have h9 : Runs (productAdapter product) (mulCost c b a) (low c)
      (work high A B A) (work high [] Q A) := by
    intro regs
    simpa only [work_binary] using Steps.mul_eval c b a regs (work high A B A)
      (by rfl) (by rfl) (by simpa [work] using htmp)
  have h10 : Runs (clear 85) (2*A.length+3) (low c)
      (work high [] Q A) (work high [] Q []) := by
    rw [h85]
    simpa only [work_29,work_update29] using he 29 (work high [] Q A)
  have h11 : Runs (copy 68 61 70) (7*H.length+5) (low c)
      (work high [] Q []) (work high H Q []) := by
    rw [h68, h61]
    have hh':work high [] Q [] 12=H:=by simpa [work,H] using hh
    simpa only [hh',work_5,List.append_nil,work_update5] using
      hc 12 5 (by decide) (by decide) (by decide) (work high [] Q []) (by simpa [work] using htmp)
  have h12 : Runs (productAdapter product) (mulCost c q h) (low c)
      (work high H Q []) (work high [] G []) := by
    intro regs
    simpa only [work_binary] using Steps.mul_eval c q h regs (work high H Q [])
      (by rfl) (by rfl) (by simpa [work] using htmp)
  have hrun:=h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq
    (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (Runs.skip (low c) (work high [] G [])))))))))))))
  simpa only [arithmetic,sequence,List.foldr_cons,List.foldr_nil,arithmeticCost,
    Nat.add_assoc,Nat.add_zero,cubic,H,O,A,a,b,q,G] using hrun

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native

theorem makeUKey_eval (x : State 8 96)
    (h70:x.stacks 70=[]) (h89:x.stacks 89=[]) (h90:x.stacks 90=[])
    (h91:x.stacks 91=[]) (h81:x.stacks 81=[]) (h92:x.stacks 92=[])
    (h93:x.stacks 93=[]) (h94:x.stacks 94=[]) :
    ∃ rr, Eval makeUKey (20*(x.stacks 88).length+50) x
      ⟨rr,Function.update x.stacks 94 (Squarefree.encodeIndex (uKey (x.stacks 88).length))⟩ := by
  simpa only [makeUKey,makeUKeyCommand,uKeyPorts,keyPorts,sequence] using
    makeUKey_command_eval x h70 h89 h90 h91 h81 h92 h93 h94

theorem shiftU_eval {n : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Squarefree.KeyMapProgram.Entry n)) (x : State 8 96)
    (hs:x.stacks 67=Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
    (hk:x.stacks 94=Squarefree.encodeIndex a)
    (hu:x.stacks 45=List.replicate u true) (hJ:x.stacks 46=List.replicate J true)
    (hclean:∀ i ∈ ([80,81,82,83,84,85,89,90,91,92]:List (Fin 96)),x.stacks i=[]) :
    ∃ k ≤ Squarefree.KeyMapProgram.budget a u J entries+2, ∃ rr,
      Eval shiftU k x ⟨rr,Function.update (Function.update x.stacks 67 []) 86
        (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped a u J entries).reverse)++x.stacks 86)⟩ := by
  simpa only [shiftU,shiftUCommand,shiftPorts,mapPorts] using
    shiftU_command_eval a u J entries x hs hk hu hJ hclean

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplier. -/

/-! Concrete preparation of the stored multiplier used by native Horner evaluation. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def byteEntries (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    List (Squarefree.KeyMapProgram.Entry n) := xs.map fun e => (e.1,RingProgram.flat e.2)

def shiftForward (a : Squarefree.Index (Fin n)) (u J : ℕ) :
    Raw (p:=p) (t:=t) (n:=n) (d:=d) → Raw (p:=p) (t:=t) (n:=n) (d:=d)
  | [] => []
  | (b,c)::rest => if (a.join b).Kept u J then (a.join b,c)::shiftForward a u J rest
      else shiftForward a u J rest

def shifted (c : Context p t n d) (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  (shiftForward (uKey n) c.u c.J xs).reverse

def prepared (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) := shifted c (cubic c minus h one)

omit [Fact p.Prime] in
theorem bytes_byteEntries (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    Product.bytes xs=Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (byteEntries xs)) := by
  simp [Product.bytes,Normalize.bytes,byteEntries,Squarefree.KeyMapProgram.encoded,
    Squarefree.Program.encodeDictionary,List.map_map,Function.comp_def]

omit [Fact p.Prime] in
theorem byteEntries_shiftForward (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    byteEntries (shiftForward a u J xs)=Squarefree.KeyMapProgram.mapped a u J (byteEntries xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b,c⟩
    by_cases hk:(a.join b).Kept u J <;>
      simp [shiftForward,byteEntries,Squarefree.KeyMapProgram.mapped,hk] at ih ⊢ <;> exact ih

omit [Fact p.Prime] in
theorem bytes_shifted (c : Context p t n d) (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    Product.bytes (shifted c xs)=Squarefree.Program.rawEntries
      (Squarefree.KeyMapProgram.encoded
        (Squarefree.KeyMapProgram.mapped (uKey n) c.u c.J (byteEntries xs)).reverse) := by
  rw [bytes_byteEntries]
  simp only [shifted,byteEntries,List.map_reverse]
  change Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded
    (byteEntries (shiftForward (uKey n) c.u c.J xs)).reverse)=_
  rw [byteEntries_shiftForward]
  rfl

/-- Sequence composition accounts for the zero-cost final skip explicitly. -/
theorem eval_sequence_append (xs ys : List (Cmd 8 96))
    {i j : ℕ} {x y z : State 8 96}
    (hx : Eval (sequence xs) i x y) (hy : Eval (sequence ys) j y z) :
    Eval (sequence (xs++ys)) (i+j) x z := by
  induction xs generalizing i x with
  | nil =>
    cases hx with
    | base hx => cases hx; simpa [sequence] using hy
  | cons a xs ih =>
    cases hx with
    | seq ha hb =>
      simpa only [sequence,List.cons_append,List.foldr_cons,Nat.add_assoc] using
        ha.seq (ih hb)

def ready (high : Data) : Prop :=
  ∀ i ∈ ([5,11,14,24,25,26,27,28,29,30,31,33,34,35,36,37,38,39]:List (Fin 40)),high i=[]

def prepareCost (c : Context p t n d) (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  arithmeticCost c minus h one+20*n+50+
    Squarefree.KeyMapProgram.budget (uKey n) c.u c.J (byteEntries (cubic c minus h one))+2

/-- Actual native execution from H and cached constants to the computed multiplier.
All low tapes and all high tapes other than output86 and U-key94 are preserved. -/
theorem prepareMultiplier_eval (c : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (ho : high 13=Product.bytes one)
    (hm : high 20=RingProgram.flat minus) (hn:(high 32).length=n) (hc:ready high) :
    ∃ k ≤ prepareCost c minus h one, ∃ rr,
      Eval prepareMultiplier k (Memory.state regs (low c) high)
        (Memory.state rr (low c) (Function.update
          (Function.update high 38 (Squarefree.encodeIndex (uKey n))) 30
            (Product.bytes (prepared c minus h one)))) := by
  let raw:=cubic c minus h one
  let high1:=work high [] (Product.bytes raw) []
  let high2:=Function.update high1 (38:Fin 40) (Squarefree.encodeIndex (uKey n))
  have hempty:work high [] [] []=high:=work_empty high
    (hc 5 (by simp)) (hc 11 (by simp)) (hc 29 (by simp))
  obtain ⟨ka,hka,r1,ha⟩:=arithmetic_runs c minus h one high hh ho hm (hc 14 (by simp)) regs
  rw [hempty] at ha
  obtain ⟨r2,hk⟩:=makeUKey_eval (Memory.state r1 (low c) high1)
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 14) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 14 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 33) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 33 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 34) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 34 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 35) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 35 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 25) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 25 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 36) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 36 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 37) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 37 (by simp))
    (by
      change Memory.tapes (low c) high1 (Memory.highPort 38) = []
      rw [Memory.tapes_high]
      simpa [high1,work] using hc 38 (by simp))
  have hn1:((Memory.state r1 (low c) high1).stacks 88).length = n := by
    change (Memory.tapes (low c) high1 (Memory.highPort 32)).length = n
    rw [Memory.tapes_high]
    simpa [high1,work] using hn
  rw [hn1] at hk
  change Eval makeUKey (20*n+50) (Memory.state r1 (low c) high1)
    ⟨r2,Function.update (Memory.tapes (low c) high1) (Memory.highPort 38)
      (Squarefree.encodeIndex (uKey n))⟩ at hk
  rw [Memory.update_high] at hk
  change Eval makeUKey (20*n+50) (Memory.state r1 (low c) high1)
    (Memory.state r2 (low c) high2) at hk
  have hclean : ∀ i ∈ ([80,81,82,83,84,85,89,90,91,92]:List (Fin 96)),
      (Memory.state r2 (low c) high2).stacks i=[] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · change Memory.tapes (low c) high2 (Memory.highPort 24)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 24 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 25)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 25 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 26)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 26 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 27)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 27 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 28)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 28 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 29)=[]
      rw [Memory.tapes_high]
      simp [high2,high1,work]
    · change Memory.tapes (low c) high2 (Memory.highPort 33)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 33 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 34)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 34 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 35)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 35 (by simp)
    · change Memory.tapes (low c) high2 (Memory.highPort 36)=[]
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using hc 36 (by simp)
  obtain ⟨ks,hks,r3,hs⟩:=shiftU_eval (uKey n) c.u c.J (byteEntries raw)
    (Memory.state r2 (low c) high2)
    (by
      change Memory.tapes (low c) high2 (Memory.highPort 11) = _
      rw [Memory.tapes_high]
      simpa [high2,high1,work] using bytes_byteEntries raw)
    (by
      change Memory.tapes (low c) high2 (Memory.highPort 38)=_
      rw [Memory.tapes_high]
      simp [high2]) (by rfl) (by rfl) hclean
  change Eval shiftU ks (Memory.state r2 (low c) high2)
    ⟨r3,Function.update (Function.update (Memory.tapes (low c) high2)
      (Memory.highPort 11) []) (Memory.highPort 30)
      (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded
        (Squarefree.KeyMapProgram.mapped (uKey n) c.u c.J (byteEntries raw)).reverse)++high2 30)⟩ at hs
  rw [Memory.update_high,Memory.update_high] at hs
  have h30:high2 30=[]:=by simpa [high2,high1,work] using hc 30 (by simp)
  have hresult : Function.update (Function.update high2 11 []) 30
      (Product.bytes (prepared c minus h one)) =
      Function.update (Function.update high 38 (Squarefree.encodeIndex (uKey n))) 30
      (Product.bytes (prepared c minus h one)) := by
    funext i
    by_cases hi:i=30 <;> by_cases hj:i=38 <;> by_cases ha:i=5 <;>
      by_cases hb:i=11 <;> by_cases hsave:i=29 <;>
      simp [high2,high1,work,hi,hj,ha,hb,hsave,hc 5 (by simp),hc 11 (by simp),hc 29 (by simp)]
  have hs' : Eval shiftU ks (Memory.state r2 (low c) high2)
      (Memory.state r3 (low c) (Function.update (Function.update high 38
        (Squarefree.encodeIndex (uKey n))) 30 (Product.bytes (prepared c minus h one)))) := by
    rw [h30,List.append_nil,←bytes_shifted c raw] at hs
    change Eval shiftU ks (Memory.state r2 (low c) high2)
      (Memory.state r3 (low c) (Function.update (Function.update high2 11 []) 30
        (Product.bytes (prepared c minus h one)))) at hs
    rw [hresult] at hs
    exact hs
  have htail:=hk.seq (hs'.seq (Eval.base (.skip _)))
  have hrun:=eval_sequence_append
    [copy 68 61 70, complement,copy 61 85 70,copy 61 67 70,clear 61,
      copy 69 61 70,add,copy 85 61 70,productAdapter product,clear 85,
      copy 68 61 70,productAdapter product] [makeUKey,shiftU] ha htail
  refine ⟨ka+(20*n+50+(ks+0)),?_,r3,?_⟩
  · dsimp only [raw] at hks
    dsimp only [prepareCost]
    omega
  · exact hrun

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplierSemantics. -/

/-! The multiplier produced by the native preparation is U H(H-1)(H-2). -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open scoped BigOperators
open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]
variable {R : Type*} [CommRing R]

private theorem decode_reverse {K C A : Type*} [AddCommMonoid C] [AddCommMonoid A]
    (atom : K → C → A) (xs : List (K×C)) :
    Squarefree.Sparse.decode atom xs.reverse=Squarefree.Sparse.decode atom xs := by
  classical
  exact Squarefree.Program.decode_reverse atom xs

omit [Fact p.Prime] in
theorem shiftForward_denote (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (f : RingProgram.Code (Word (baseWidth p t)) d → R)
    (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    Squarefree.Sparse.denote (MomentsProgram.Dictionary.denoteTable f (shiftForward a u J xs))=
      Squarefree.canonical u J (Squarefree.Sparse.atom a 1 *
        Squarefree.Sparse.denote (MomentsProgram.Dictionary.denoteTable f xs)) := by
  induction xs with
  | nil => simp [shiftForward,MomentsProgram.Dictionary.denoteTable,Squarefree.Sparse.denote,
      Squarefree.Sparse.decode]
  | cons x xs ih =>
    rcases x with ⟨b,c⟩
    by_cases hk:(a.join b).Kept u J
    all_goals
      simp only [shiftForward,hk,ite_true,ite_false,MomentsProgram.Dictionary.denoteTable,
        List.map_cons,Squarefree.Sparse.denote,Squarefree.Sparse.decode,mul_add,map_add,
        Squarefree.Sparse.atom_mul,one_mul,Squarefree.Sparse.canonical_atom,ite_true,ite_false,
        zero_add] at ih ⊢
      first
      | exact congrArg (fun z => Squarefree.Sparse.atom (a.join b) (f c)+z) ih
      | exact ih

theorem shifted_denote (c : Context p t n d) (φ : ZMod (p^t) →+* R) (basis : Fin d → R)
    (xs : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    storedDenote p t c.modulus c.cache φ basis (shifted c xs)=
      Squarefree.canonical c.u c.J (Squarefree.Sparse.atom (uKey n) 1 *
        storedDenote p t c.modulus c.cache φ basis xs) := by
  unfold storedDenote shifted
  rw [MomentsProgram.Dictionary.denoteTable_reverse]
  change Squarefree.Sparse.decode _ _ = _
  rw [decode_reverse]
  exact shiftForward_denote _ _ _ _ _

/-- Cached one and minus-one are checked by their represented ring meanings;
no premise supplies the desired multiplier or its denotation. -/
theorem prepared_denote (c : Context p t n d) (φ : ZMod (p^t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i*basis j=∑ k,φ (wordValue p t (c.table i j k))*basis k)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (hminus : RingProgram.denote (RingProgram.scalarRing p t c.modulus c.cache) φ basis minus = -1)
    (h one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (honeKeys : (Squarefree.Sparse.keys one).Nodup)
    (hone : storedDenote p t c.modulus c.cache φ basis one=Squarefree.canonical c.u c.J 1)
    (H : Squarefree.Jet (Fin n) R)
    (hh : storedDenote p t c.modulus c.cache φ basis h=Squarefree.canonical c.u c.J H) :
    storedDenote p t c.modulus c.cache φ basis (prepared c minus h one)=
      Squarefree.canonical c.u c.J
        (Squarefree.Sparse.atom (uKey n) 1 * IdempotentProgram.hValue H) := by
  let a:=complemented c minus h one
  let b:=plus c a one
  let q:=mul c b a
  have hscaled : storedDenote p t c.modulus c.cache φ basis (Squarefree.ScaleProgram.scaled p t c.modulus c.cache c.table minus h) = -storedDenote p t c.modulus c.cache φ basis h := by
    exact Squarefree.ScaleProgram.denote_neg p t c.modulus c.cache φ basis c.table htable minus hminus h
  have ha : storedDenote p t c.modulus c.cache φ basis a=Squarefree.canonical c.u c.J (1-H) := by
    change storedDenote p t c.modulus c.cache φ basis (addStored p t c.modulus c.cache
      (Squarefree.ScaleProgram.scaled p t c.modulus c.cache c.table minus h) one)=_
    rw [addStored_denote p t c.modulus c.cache φ basis _ _ honeKeys,hscaled,hone,hh]
    have hs : Squarefree.canonical c.u c.J (1-H) =
        Squarefree.canonical c.u c.J 1 - Squarefree.canonical c.u c.J H :=
      map_sub (Squarefree.canonical (V:=Fin n) (R:=R) c.u c.J) 1 H
    rw [hs]
    abel
  have hb : storedDenote p t c.modulus c.cache φ basis b=Squarefree.canonical c.u c.J (2-H) := by
    change storedDenote p t c.modulus c.cache φ basis (addStored p t c.modulus c.cache a one)=_
    rw [addStored_denote p t c.modulus c.cache φ basis _ _ honeKeys,ha,hone,←map_add]
    congr 1
    ring
  have hq : storedDenote p t c.modulus c.cache φ basis q=Squarefree.canonical c.u c.J ((2-H)*(1-H)) := by
    change storedDenote p t c.modulus c.cache φ basis (mulStored p t c.modulus c.cache c.table c.u c.J b a)=_
    rw [mulStored_denote p t c.modulus c.cache φ basis c.table htable,hb,ha,Squarefree.canonical_mul]
  have hidempotent : ((2-H)*(1-H))*H = IdempotentProgram.hValue H := by
    unfold IdempotentProgram.hValue
    ring
  have hg : storedDenote p t c.modulus c.cache φ basis (cubic c minus h one)=Squarefree.canonical c.u c.J (IdempotentProgram.hValue H) := by
    change storedDenote p t c.modulus c.cache φ basis (mulStored p t c.modulus c.cache c.table c.u c.J q h)=_
    rw [mulStored_denote p t c.modulus c.cache φ basis c.table htable,hq,hh,Squarefree.canonical_mul]
    exact congrArg (Squarefree.canonical c.u c.J) hidempotent
  change storedDenote p t c.modulus c.cache φ basis (shifted c (cubic c minus h one))=_
  rw [shifted_denote c φ basis,hg,Moments.canonical_mul_right]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

end OAI.Algorithms
