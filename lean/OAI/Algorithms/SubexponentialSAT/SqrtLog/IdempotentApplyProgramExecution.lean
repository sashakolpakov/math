import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramReadScalar
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramMemory
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramStored
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramTape

namespace OAI.Algorithms


/-! Native high-register services for the quadratic and Horner steps. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram
namespace Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

/-- Workspace condition for the native scalar reader, expressed only in high memory. -/
def scalarReady (dst : Fin 40) (high : Data) : Prop :=
  ∀ i ∈ ([14,24,25,26,27,33,34,35,36,dst] : List (Fin 40)), high i=[]

omit [Fact (Nat.Prime p)] in
theorem scalar_eval (c : Context p t n d) (hd : 0 < d) (regs : Regs) (high : Data)
    (dst : Fin 40) (hdst : dst=5 ∨ dst=11) (word : RingProgram.ScalarCode p t)
    (tail : List Bool) (hsource : high 23=word.val.reverse++tail)
    (hshape : (high 32).length=n) (hready : scalarReady dst high) :
    ∃ rr, Eval (scalarConstant (Memory.highPort dst)) (ReadScalar.wordCost (baseWidth p t) d n)
      (Memory.state regs (low c) high)
      (Memory.state rr (low c) (Function.update (Function.update high 23 tail) dst
        (Product.bytes (constant c word)))) := by
  have hwork : ∀ i ∈ ReadScalar.scalarWork (Memory.highPort dst),
      (Memory.state regs (low c) high).stacks i=[] := by
    rcases hdst with rfl | rfl <;>
      intro i hi <;>
      simp only [ReadScalar.scalarWork,List.mem_cons,List.not_mem_nil,or_false] at hi <;>
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | exact hready 14 (by simp) | exact hready 24 (by simp) | exact hready 25 (by simp) | exact hready 26 (by simp) | exact hready 27 (by simp) | exact hready 33 (by simp) | exact hready 34 (by simp) | exact hready 35 (by simp) | exact hready 36 (by simp) | simpa only [Memory.state,Memory.tapes_high] using hready 5 (by simp) | simpa only [Memory.state,Memory.tapes_high] using hready 11 (by simp)
  obtain ⟨rr,he⟩:=ReadScalar.scalar_words_eval hd (Memory.state regs (low c) high)
    (Memory.highPort dst) (by rcases hdst with rfl|rfl <;> decide) c.cache.zero word tail
    (by change c.width.length=baseWidth p t; exact c.widthLength)
    rfl rfl (by change (high 32).length=n; exact hshape)
    (by change high 23=word.val.reverse++tail; exact hsource) hwork
  refine ⟨rr,?_⟩
  change Eval _ _ _ ⟨rr, Function.update
    (Function.update (Memory.tapes (low c) high) (Memory.highPort 23) tail)
    (Memory.highPort dst) (Product.bytes (constant c word))⟩ at he
  simpa only [Memory.update_high,Memory.state] using he

/-- Copy the persistent hash into the operand port, then invoke the real sparse product. -/
theorem mul_hash_eval (c : Context p t n d) (a h : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data) (ha : high 11=Product.bytes a)
    (hh : high 12=Product.bytes h) (hempty : high 5=[]) (htmp : high 14=[]) :
    ∃ cost ≤ 7*(Product.bytes h).length+5+mulCost c a h, ∃ rr,
      Eval (.seq (copy 68 61 70) (productAdapter product)) cost
        (Memory.state regs (low c) high)
        (Memory.state rr (low c) (binaryResult high (Product.bytes (mul c a h)))) := by
  let next:=Function.update high (5:Fin 40) (Product.bytes h)
  have hc:=copy_high_high regs (low c) high 12 5 14 (by decide) (by decide) (by decide) htmp
  simp only [hh,hempty,List.append_nil] at hc
  obtain ⟨k,hk,rr,he⟩:=mul_eval c a h (readRegs regs 0 1 none) next
    (by simpa [next] using ha) (by simp [next]) (by simpa [next] using htmp)
  refine ⟨7*(Product.bytes h).length+5+k,by omega,rr,?_⟩
  have hb : binaryResult next (Product.bytes (mul c a h))=
      binaryResult high (Product.bytes (mul c a h)) := by
    funext i
    by_cases hi : i=11 <;> by_cases hj : i=5 <;>
      simp_all [binaryResult,next]
  rw [hb] at he
  exact hc.seq he


theorem binaryResult_clean (high : Data) (result : List Bool) (h5 : high 5=[]) :
    binaryResult high result=Function.update high 11 result := by
  funext i
  by_cases hi : i=11 <;> by_cases hj : i=5 <;>
    simp_all [binaryResult]

theorem mul_hash_clean (c : Context p t n d) (a h : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data) (ha : high 11=Product.bytes a)
    (hh : high 12=Product.bytes h) (hempty : high 5=[]) (htmp : high 14=[]) :
    ∃ cost ≤ 7*(Product.bytes h).length+5+mulCost c a h, ∃ rr,
      Eval (.seq (copy 68 61 70) (productAdapter product)) cost
        (Memory.state regs (low c) high)
        (Memory.state rr (low c) (Function.update high 11 (Product.bytes (mul c a h)))) := by
  obtain ⟨cost,hcost,rr,he⟩:=mul_hash_eval c a h regs high ha hh hempty htmp
  rw [binaryResult_clean _ _ hempty] at he
  exact ⟨cost,hcost,rr,he⟩

/-- The constant term is read from the real reversed coefficient stream. -/
theorem add_constant_eval (c : Context p t n d) (hd : 0 < d)
    (a : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (word : RingProgram.ScalarCode p t)
    (regs : Regs) (high : Data) (tail : List Bool)
    (ha : high 11=Product.bytes a) (hsource : high 23=word.val.reverse++tail)
    (hshape : (high 32).length=n) (hready : scalarReady 5 high) :
    ∃ cost ≤ ReadScalar.wordCost (baseWidth p t) d n+addCost c a (constant c word), ∃ rr,
      Eval (.seq (scalarConstant 61) add) cost (Memory.state regs (low c) high)
        (Memory.state rr (low c) (Function.update (Function.update high 23 tail) 11
          (Product.bytes (plus c a (constant c word))))) := by
  obtain ⟨r1,hs⟩:=scalar_eval c hd regs high 5 (Or.inl rfl) word tail hsource hshape hready
  let next:=Function.update (Function.update high (23:Fin 40) tail) 5
    (Product.bytes (constant c word))
  obtain ⟨cost,hcost,rr,he⟩:=add_eval c a (constant c word) r1 next
    (by simpa [next] using ha) (by simp [next])
    (by simpa [next] using hready 14 (by simp))
  have h5 : high 5=[]:=hready 5 (by simp)
  have hb : binaryResult next (Product.bytes (plus c a (constant c word)))=
      Function.update (Function.update high 23 tail) 11
        (Product.bytes (plus c a (constant c word))) := by
    funext i
    by_cases hi : i=11 <;> by_cases hj : i=5 <;> by_cases hk : i=23 <;>
      simp_all [binaryResult,next]
  rw [hb] at he
  exact ⟨_,Nat.add_le_add_left hcost _,rr,hs.seq he⟩

/-- Reassociation does not insert instructions or alter the measured cost. -/
theorem eval_seq_assoc {r s : ℕ} (a b c : Cmd r s) (n : ℕ) (x y : State r s) :
    Eval (.seq (.seq a b) c) n x y ↔ Eval (.seq a (.seq b c)) n x y := by
  constructor
  · intro h
    cases h with
    | seq hab hc =>
      cases hab with
      | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)
  · intro h
    cases h with
    | seq ha hbc =>
      cases hbc with
      | seq hb hc => simpa only [Nat.add_assoc] using (ha.seq hb).seq hc


theorem seq_tail {r s : ℕ} {a b c : Cmd r s} {n m : ℕ} {x y z : State r s}
    (hab : Eval (.seq a b) n x y) (hc : Eval c m y z) :
    Eval (.seq a (.seq b c)) (n+m) x z := by
  cases hab with
  | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)

end Steps
end SubexponentialSAT.SqrtLog.IdempotentApplyProgram


/-! Complete native evaluation of one degree-two coefficient digit. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

def quadraticCost (ctx : Context p t n d) (h : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (v : Triple (RingProgram.ScalarCode p t)) : ℕ :=
  let ch:=mul ctx (constant ctx v.c) h
  let chb:=plus ctx ch (constant ctx v.b)
  let chbh:=mul ctx chb h
  3*ReadScalar.wordCost (baseWidth p t) d n +
    2*(7*(Product.bytes h).length+5)+
    mulCost ctx (constant ctx v.c) h+addCost ctx ch (constant ctx v.b)+
    mulCost ctx chb h+addCost ctx chbh (constant ctx v.a)

theorem quadratic_eval (ctx : Context p t n d) (hd : 0 < d)
    (h : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (v : Triple (RingProgram.ScalarCode p t))
    (regs : Regs) (high : Data) (tail : List Bool)
    (hh : high 12=Product.bytes h) (hempty : high 5=[])
    (hsource : high 23=v.c.val.reverse++(v.b.val.reverse++(v.a.val.reverse++tail)))
    (hshape : (high 32).length=n) (hready : scalarReady 11 high) :
    ∃ cost ≤ quadraticCost ctx h v, ∃ rr,
      Eval tripleStep cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx) (Function.update (Function.update high 23 tail) 11
          (Product.bytes (tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v)))) := by
  let t1:=v.b.val.reverse++(v.a.val.reverse++tail)
  let t2:=v.a.val.reverse++tail
  let c:=constant ctx v.c
  let ch:=mul ctx c h
  let chb:=plus ctx ch (constant ctx v.b)
  let chbh:=mul ctx chb h
  let out:=plus ctx chbh (constant ctx v.a)
  let h1:=Function.update (Function.update high (23:Fin 40) t1) 11 (Product.bytes c)
  obtain ⟨r1,e1⟩:=scalar_eval ctx hd regs high 11 (Or.inr rfl) v.c t1 hsource hshape hready
  change Eval (scalarConstant 67) _ _ (Memory.state r1 (low ctx) h1) at e1
  obtain ⟨k2,b2,r2,e2⟩:=mul_hash_clean ctx c h r1 h1
    (by simp [h1]) (by simpa [h1] using hh)
    (by simpa [h1] using hempty) (by simpa [h1] using hready 14 (by simp))
  let h2:=Function.update h1 (11:Fin 40) (Product.bytes ch)
  change Eval _ _ _ (Memory.state r2 (low ctx) h2) at e2
  have ready2 : scalarReady 5 h2 := by
    simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false] at hready ⊢
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [h2,h1,hempty,hready]
  obtain ⟨k3,b3,r3,e3⟩:=add_constant_eval ctx hd ch v.b r2 h2 t2
    (by simp [h2]) (by simp [h2,h1,t1,t2])
    (by simpa [h2,h1] using hshape) ready2
  let h3:=Function.update (Function.update h2 (23:Fin 40) t2) 11 (Product.bytes chb)
  change Eval _ _ _ (Memory.state r3 (low ctx) h3) at e3
  obtain ⟨k4,b4,r4,e4⟩:=mul_hash_clean ctx chb h r3 h3
    (by simp [h3]) (by simpa [h3,h2,h1] using hh)
    (by simpa [h3,h2,h1] using hempty)
    (by simpa [h3,h2,h1] using hready 14 (by simp))
  let h4:=Function.update h3 (11:Fin 40) (Product.bytes chbh)
  change Eval _ _ _ (Memory.state r4 (low ctx) h4) at e4
  have ready4 : scalarReady 5 h4 := by
    simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false] at hready ⊢
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [h4,h3,h2,h1,hempty,hready]
  obtain ⟨k5,b5,r5,e5⟩:=add_constant_eval ctx hd chbh v.a r4 h4 tail
    (by simp [h4]) (by simp [h4,h3,t2])
    (by simpa [h4,h3,h2,h1] using hshape) ready4
  let h5:=Function.update (Function.update h4 (23:Fin 40) tail) 11 (Product.bytes out)
  change Eval _ _ _ (Memory.state r5 (low ctx) h5) at e5
  have he:=e1.seq (seq_tail e2 (seq_tail e3 (seq_tail e4 (seq_tail e5
    (Eval.base (StructuredProgram.Eval.skip (Memory.state r5 (low ctx) h5)))))))
  have hh5 : h5=Function.update (Function.update high 23 tail) 11 (Product.bytes out) := by
    funext i
    by_cases hi : i=11 <;> by_cases hj : i=23 <;>
      simp_all [h5,h4,h3,h2,h1]
  rw [hh5] at he
  refine ⟨ReadScalar.wordCost (baseWidth p t) d n+(k2+(k3+(k4+(k5+0)))),?_,r5,?_⟩
  · dsimp [quadraticCost,c,ch,chb,chbh] at *
    omega
  · exact he

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps


/-! The native Horner accumulator update, including every move and cleanup. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem move_eval (regs : Regs) (low : Fin 56 → List Bool) (high : Data)
    (src dst : Fin 40) (hne : src≠dst) (hs : src≠14) (hd : dst≠14)
    (hempty : high dst=[]) (htmp : high 14=[]) :
    Eval (.seq (copy (Memory.highPort src) (Memory.highPort dst) 70)
        (clear (Memory.highPort src))) (9*(high src).length+8)
      (Memory.state regs low high)
      (Memory.state (readRegs (readRegs regs 0 1 none) 0 1 none) low
        (Function.update (Function.update high src []) dst (high src))) := by
  have hc:=copy_high_high regs low high src dst 14 hne hs hd.symm htmp
  simp only [hempty,List.append_nil] at hc
  have he:=Memory.clear_high (readRegs regs 0 1 none) low
    (Function.update high dst (high src)) src
  simp only [Function.update_of_ne hne] at he
  have hstate : Function.update (Function.update high dst (high src)) src []=
      Function.update (Function.update high src []) dst (high src) := by
    funext i
    by_cases hi : i=src <;> by_cases hj : i=dst <;> simp_all
  rw [hstate] at he
  convert hc.seq he using 1 <;> first | rfl | omega

def accumulatorCost (ctx : Context p t n d)
    (e a g : Raw (p:=p) (t:=t) (n:=n) (d:=d)) : ℕ :=
  let ag:=mul ctx a g
  let out:=plus ctx ag e
  18*(Product.bytes e).length+9*(Product.bytes a).length+
    7*(Product.bytes g).length+9*(Product.bytes out).length+37+
      mulCost ctx a g+addCost ctx ag e

theorem accumulator_eval (ctx : Context p t n d)
    (e a g : Raw (p:=p) (t:=t) (n:=n) (d:=d)) (regs : Regs) (high : Data)
    (he : high 11=Product.bytes e) (ha : high 31=Product.bytes a)
    (hg : high 30=Product.bytes g) (h5 : high 5=[]) (h29 : high 29=[])
    (htmp : high 14=[]) :
    ∃ cost ≤ accumulatorCost ctx e a g, ∃ rr,
      Eval accumulatorStep cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx) (Function.update (Function.update high 11 []) 31
          (Product.bytes (plus ctx (mul ctx a g) e)))) := by
  let r1:=readRegs (readRegs regs 0 1 none) 0 1 none
  let h1:=Function.update (Function.update high (11:Fin 40) []) 29 (Product.bytes e)
  have e1:=move_eval regs (low ctx) high 11 29 (by decide) (by decide) (by decide) h29 htmp
  simp only [he] at e1
  change Eval _ _ _ (Memory.state r1 (low ctx) h1) at e1
  let r2:=readRegs (readRegs r1 0 1 none) 0 1 none
  let h2:=Function.update (Function.update h1 (31:Fin 40) []) 11 (Product.bytes a)
  have e2:=move_eval r1 (low ctx) h1 31 11 (by decide) (by decide) (by decide)
    (by simp [h1]) (by simpa [h1] using htmp)
  have ha1 : h1 31=Product.bytes a:=by simpa [h1] using ha
  simp only [ha1] at e2
  change Eval _ _ _ (Memory.state r2 (low ctx) h2) at e2
  let r3:=readRegs r2 0 1 none
  let h3:=Function.update h2 (5:Fin 40) (Product.bytes g)
  have e3:=copy_high_high r2 (low ctx) h2 30 5 14 (by decide) (by decide) (by decide)
    (by simpa [h2,h1] using htmp)
  have hg2 : h2 30=Product.bytes g:=by simpa [h2,h1] using hg
  have hz2 : h2 5=[]:=by simpa [h2,h1] using h5
  simp only [hg2,hz2,List.append_nil] at e3
  change Eval _ _ _ (Memory.state r3 (low ctx) h3) at e3
  obtain ⟨k4,b4,r4,e4⟩:=mul_eval ctx a g r3 h3
    (by simp [h3,h2]) (by simp [h3]) (by simpa [h3,h2,h1] using htmp)
  let h4:=binaryResult h3 (Product.bytes (mul ctx a g))
  let r5:=readRegs (readRegs r4 0 1 none) 0 1 none
  let h5':=Function.update (Function.update h4 (29:Fin 40) []) 5 (Product.bytes e)
  have e5:=move_eval r4 (low ctx) h4 29 5 (by decide) (by decide) (by decide)
    (by simp [h4,binaryResult]) (by simpa [h4,binaryResult,h3,h2,h1] using htmp)
  have he4 : h4 29=Product.bytes e:=by simp [h4,binaryResult,h3,h2,h1]
  simp only [he4] at e5
  change Eval _ _ _ (Memory.state r5 (low ctx) h5') at e5
  obtain ⟨k6,b6,r6,e6⟩:=add_eval ctx (mul ctx a g) e r5 h5'
    (by simp [h5',h4,binaryResult]) (by simp [h5'])
    (by simpa [h5',h4,binaryResult,h3,h2,h1] using htmp)
  let h6:=binaryResult h5' (Product.bytes (plus ctx (mul ctx a g) e))
  have e7:=move_eval r6 (low ctx) h6 11 31 (by decide) (by decide) (by decide)
    (by simp [h6,binaryResult,h5',h4,h3,h2])
    (by simpa [h6,binaryResult,h5',h4,h3,h2,h1] using htmp)
  have hout6 : h6 11=Product.bytes (plus ctx (mul ctx a g) e):=by simp [h6,binaryResult]
  simp only [hout6] at e7
  let rf:=readRegs (readRegs r6 0 1 none) 0 1 none
  let out:=Function.update (Function.update h6 (11:Fin 40) []) 31
    (Product.bytes (plus ctx (mul ctx a g) e))
  have hrun:=seq_tail e1 (seq_tail e2 (e3.seq (e4.seq (seq_tail e5 (e6.seq (seq_tail e7
    (Eval.base (StructuredProgram.Eval.skip (Memory.state rf (low ctx) out)))))))))
  have hout : out=Function.update (Function.update high 11 []) 31
      (Product.bytes (plus ctx (mul ctx a g) e)) := by
    funext i
    by_cases hi : i=11 <;> by_cases hj : i=31 <;> by_cases hk : i=29 <;>
      by_cases hl : i=5 <;>
      simp_all [out,h6,binaryResult,h5',h4,h3,h2,h1]
  rw [hout] at hrun
  refine ⟨_,?_,rf,hrun⟩
  dsimp [accumulatorCost]
  omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps


/-! Measured descending Horner loop over the actual computed coefficient tape. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

def loopResult (ctx : Context p t n d) (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    List (Triple (RingProgram.ScalarCode p t)) → Raw (p:=p) (t:=t) (n:=n) (d:=d) → Raw (p:=p) (t:=t) (n:=n) (d:=d)
  | [],a => a
  | v::vs,a => loopResult ctx h g vs
      (plus ctx (mul ctx a g) (tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v))

def loopCost (ctx : Context p t n d) (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    List (Triple (RingProgram.ScalarCode p t)) → Raw (p:=p) (t:=t) (n:=n) (d:=d) → ℕ
  | [],_ => 1
  | v::vs,a =>
      let e:=tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v
      quadraticCost ctx h v+accumulatorCost ctx e a g+2+
        loopCost ctx h g vs (plus ctx (mul ctx a g) e)

theorem loopResult_eq (ctx : Context p t n d) (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Raw (p:=p) (t:=t) (n:=n) (d:=d)) :
    loopResult ctx h g vs a=descendingStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h g vs a := by
  induction vs generalizing a with
  | nil => rfl
  | cons v vs ih => exact ih _

theorem peek_eval (regs : Regs) (l : Fin 56 → List Bool) (high : Data) :
    Eval peekCoefficients 1 (Memory.state regs l high)
      (Memory.state (readRegs regs 0 7 (high 23).head?) l high) := by
  exact .base (.atom _ _)

theorem loop_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (hg : high 30=Product.bytes g)
    (ha : high 31=Product.bytes a) (h5 : high 5=[]) (h29 : high 29=[])
    (hsource : high 23=descendingTape vs)
    (hshape : (high 32).length=n) (hready : scalarReady 11 high)
    (htest : regs 7=(high 23).head?.isSome) :
    ∃ cost ≤ loopCost ctx h g vs a, ∃ rr,
      Eval (.while 7 hornerStep) cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx) (Function.update (Function.update high 23 []) 31
          (Product.bytes (loopResult ctx h g vs a)))) := by
  induction vs generalizing regs high a with
  | nil =>
    have hs : high 23=[]:=hsource
    have ht : regs 7=false:=by simpa [hs] using htest
    have heq : Function.update (Function.update high 23 []) 31 (Product.bytes a)=high := by
      funext i
      by_cases hi : i=23 <;> by_cases hj : i=31 <;> simp_all
    refine ⟨1,by simp [loopCost],regs,?_⟩
    simpa only [loopResult,heq] using (Eval.while_false (a:=Memory.state regs (low ctx) high) (body:=hornerStep) ht)
  | cons v vs ih =>
    let e:=tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v
    let next:=plus ctx (mul ctx a g) e
    let hq:=Function.update (Function.update high (23:Fin 40) (descendingTape vs)) 11 (Product.bytes e)
    obtain ⟨kq,bq,rq,eq⟩:=quadratic_eval ctx hd h v regs high (descendingTape vs) hh h5
      (by simpa only [descendingTape_cons] using hsource) hshape hready
    change Eval tripleStep kq _ (Memory.state rq (low ctx) hq) at eq
    obtain ⟨ka,ba,ra,ea⟩:=accumulator_eval ctx e a g rq hq
      (by simp [hq]) (by simpa [hq] using ha) (by simpa [hq] using hg)
      (by simpa [hq] using h5) (by simpa [hq] using h29)
      (by simpa [hq] using hready 14 (by simp))
    let hr:=Function.update (Function.update hq (11:Fin 40) []) 31 (Product.bytes next)
    change Eval accumulatorStep ka _ (Memory.state ra (low ctx) hr) at ea
    let rp:=readRegs ra 0 7 (hr 23).head?
    have ep:=peek_eval ra (low ctx) hr
    have rready : scalarReady 11 hr := by
      simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false] at hready ⊢
      intro i hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [hr,hq,hready]
    obtain ⟨kl,bl,rl,el⟩:=ih next rp hr
      (by simpa [hr,hq] using hh) (by simpa [hr,hq] using hg) (by simp [hr])
      (by simpa [hr,hq] using h5) (by simpa [hr,hq] using h29)
      (by simp [hr,hq]) (by simpa [hr,hq] using hshape) rready
      (by simp [rp,readRegs])
    have test : regs 7=true := by
      rw [htest,hsource]
      cases htape : descendingTape (v::vs) with
      | nil => exact False.elim ((descendingTape_cons_ne_nil hB v vs) htape)
      | cons b bs => rfl
    have hb : Eval hornerStep (kq+(ka+1)) (Memory.state regs (low ctx) high)
        (Memory.state rp (low ctx) hr) := eq.seq (ea.seq ep)
    have he:=Eval.while_true test hb el
    have hout : Function.update (Function.update hr 23 []) 31
        (Product.bytes (loopResult ctx h g vs next))=
        Function.update (Function.update high 23 []) 31
          (Product.bytes (loopResult ctx h g (v::vs) a)) := by
      funext i
      have hz : high 11=[]:=hready 11 (by simp)
      by_cases hi : i=11 <;> by_cases hj : i=23 <;> by_cases hk : i=31 <;>
        simp_all [hr,hq,loopResult,next,e,Function.update_apply]
    rw [hout] at he
    refine ⟨kq+(ka+1)+kl+1,?_,rl,he⟩
    dsimp only [next,e] at bl ba
    dsimp only [loopCost]
    omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

abbrev applyLoop : Cmd 8 96 := sequence
  [copy 78 84 70, transfer 84 79, peekCoefficients,
   .while 7 hornerStep, copy 87 67 70, clear 87, clear 86, clear 94]

def applyLoopCost (ctx : Context p t n d) (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (key : List Bool) : ℕ :=
  10*(triplesTape vs).length+
    9*(Product.bytes (loopResult ctx h g vs.reverse [])).length+
    2*(Product.bytes g).length+2*key.length+23+loopCost ctx h g vs.reverse []

/-- Tape reversal, native Horner evaluation and final scratch reclamation. -/
theorem applyLoop_eval (ctx : Context p t n d) (hd : 0 < d) (hB : 0 < baseWidth p t)
    (h g : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (vs : List (Triple (RingProgram.ScalarCode p t))) (regs : Regs) (high : Data)
    (hh : high 12=Product.bytes h) (hg : high 30=Product.bytes g)
    (htape : high 22=triplesTape vs) (h5 : high 5=[]) (h23 : high 23=[])
    (h28 : high 28=[]) (h29 : high 29=[]) (h31 : high 31=[])
    (hshape : (high 32).length=n) (hready : scalarReady 11 high) :
    ∃ cost ≤ applyLoopCost ctx h g vs (high 38), ∃ rr,
      Eval applyLoop cost (Memory.state regs (low ctx) high)
        (Memory.state rr (low ctx)
          (Function.update (Function.update (Function.update high 30 []) 38 []) 11
            (Product.bytes (loopResult ctx h g vs.reverse [])))) := by
  let tape:=triplesTape vs
  let r1:=readRegs regs 0 1 none
  let h1:=Function.update high (28:Fin 40) tape
  have e1:=copy_high_high regs (low ctx) high 22 28 14 (by decide) (by decide) (by decide)
    (hready 14 (by simp))
  simp only [htape,h28,List.append_nil] at e1
  change Eval _ _ _ (Memory.state r1 (low ctx) h1) at e1
  let r2:=readRegs r1 0 1 none
  let h2:=Function.update (Function.update h1 (28:Fin 40) []) 23 tape.reverse
  have e2:=transfer_high_high r1 (low ctx) h1 28 23 (by decide)
  have ht1 : h1 28=tape:=by simp [h1]
  have h23' : h1 23=[]:=by simpa [h1] using h23
  simp only [ht1,h23',List.append_nil] at e2
  change Eval _ _ _ (Memory.state r2 (low ctx) h2) at e2
  let rp:=readRegs r2 0 7 (h2 23).head?
  have ep:=peek_eval r2 (low ctx) h2
  have ready2 : scalarReady 11 h2 := by
    simp only [scalarReady,List.mem_cons,List.not_mem_nil,or_false] at hready ⊢
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [h2,h1,hready]
  obtain ⟨kl,bl,rl,el⟩:=loop_eval ctx hd hB h g vs.reverse [] rp h2
    (by simpa [h2,h1] using hh) (by simpa [h2,h1] using hg)
    (by simpa [h2,h1,Product.bytes,Normalize.bytes,Squarefree.Program.encodeDictionary,
      Squarefree.Program.rawEntries] using h31)
    (by simpa [h2,h1] using h5) (by simpa [h2,h1] using h29)
    (by simp [h2,tape,triplesTape_reverse])
    (by simpa [h2,h1] using hshape) ready2 (by simp [rp,readRegs])
  let result:=Product.bytes (loopResult ctx h g vs.reverse [])
  let hl:=Function.update (Function.update h2 (23:Fin 40) []) 31 result
  change Eval _ _ _ (Memory.state rl (low ctx) hl) at el
  have em:=move_eval rl (low ctx) hl 31 11 (by decide) (by decide) (by decide)
    (by simpa [hl,h2,h1] using hready 11 (by simp))
    (by simpa [hl,h2,h1] using hready 14 (by simp))
  have hres : hl 31=result:=by simp [hl]
  simp only [hres] at em
  let rm:=readRegs (readRegs rl 0 1 none) 0 1 none
  let hm:=Function.update (Function.update hl (31:Fin 40) []) 11 result
  change Eval _ _ _ (Memory.state rm (low ctx) hm) at em
  have eg:=Memory.clear_high rm (low ctx) hm 30
  have hgm : hm 30=Product.bytes g:=by simpa [hm,hl,h2,h1] using hg
  simp only [hgm] at eg
  let rg:=readRegs rm 0 1 none
  let hgc:=Function.update hm (30:Fin 40) []
  have ek:=Memory.clear_high rg (low ctx) hgc 38
  have hkey : hgc 38=high 38:=by simp [hgc,hm,hl,h2,h1]
  simp only [hkey] at ek
  let rk:=readRegs rg 0 1 none
  let hk:=Function.update hgc (38:Fin 40) []
  have eall:=e1.seq (e2.seq (ep.seq (el.seq (seq_tail em (eg.seq (ek.seq
    (Eval.base (StructuredProgram.Eval.skip (Memory.state rk (low ctx) hk)))))))))
  have hout : hk=Function.update (Function.update (Function.update high 30 []) 38 []) 11 result := by
    funext i
    by_cases hi11 : i=11
    · subst i
      simp [hk,hgc,hm,hl,h2,h1]
    by_cases hi30 : i=30
    · subst i
      simp [hk,hgc,hm,hl,h2,h1]
    by_cases hi38 : i=38
    · subst i
      simp [hk,hgc,hm,hl,h2,h1]
    by_cases hi23 : i=23
    · subst i
      simp [hk,hgc,hm,hl,h2,h1,h23]
    by_cases hi28 : i=28
    · subst i
      simp [hk,hgc,hm,hl,h2,h1,h28]
    by_cases hi31 : i=31
    · subst i
      simp [hk,hgc,hm,hl,h2,h1,h31]
    simp [hk,hgc,hm,hl,h2,h1,hi11,hi30,hi38,hi23,hi28,hi31]
  rw [hout] at eall
  refine ⟨_,?_,rk,eall⟩
  dsimp [applyLoopCost,tape,result] at *
  omega

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
