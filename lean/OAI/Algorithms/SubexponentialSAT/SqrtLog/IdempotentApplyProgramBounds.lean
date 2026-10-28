import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramBoundsCapacity
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramExecution

namespace OAI.Algorithms

/-! Fixed polynomial envelopes for the concrete degree-two coefficient and
Horner machines. Every byte copy, dictionary scan, product and tape reversal
in the native cost definitions is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

def Bounded (ctx : Context p t n d) (vars : Finset (Fin n))
    (a : Stored p t (n:=n) (d:=d)) : Prop :=
  Valid vars ctx.u ctx.J a ∧ a.length ≤ capacity vars ctx.u ctx.J

omit [Fact (Nat.Prime p)] in
theorem good_bounded (ctx : Context p t n d) (vars : Finset (Fin n))
    (a : Stored p t (n:=n) (d:=d)) (ha : Good vars ctx.u ctx.J a) :
    Bounded ctx vars a := ⟨ha.1, length_le_capacity vars ctx.u ctx.J a ha⟩

omit [Fact (Nat.Prime p)] in
theorem bounded_bytes (ctx : Context p t n d) (vars : Finset (Fin n))
    (a : Stored p t (n:=n) (d:=d)) (ha : Bounded ctx vars a) :
    (Product.bytes a).length ≤
      byteCapacity n (baseWidth p t) d ctx.u ctx.J (capacity vars ctx.u ctx.J) :=
  (Product.bytes_length_le a (n+ctx.u+ctx.J)
    (valid_keyBound vars ctx.u ctx.J a ha.1)).trans (Nat.mul_le_mul_right _ ha.2)

def mulEnvelope (B d n u J N : ℕ) : ℕ :=
  29*byteCapacity n B d u J N +
    N*(Product.stepEnvelope B d n u J (N*N) N+2)+30

def addEnvelope (B d n u J N : ℕ) : ℕ :=
  36*byteCapacity n B d u J N+9*d+
    N*(220*(2*N+1)*(n+u+J+d*B+1)+MomentsProgram.Dictionary.codeBranchBudget B d+2)+44

def wordEnvelope (B d n : ℕ) : ℕ :=
  20*B+7*d+d*(7*B+7)+7*(d*B)+15*n+65

def quadraticEnvelope (B d n u J N : ℕ) : ℕ :=
  3*wordEnvelope B d n+2*(7*byteCapacity n B d u J N+5)+
    2*mulEnvelope B d n u J N+2*addEnvelope B d n u J N

def accumulatorEnvelope (B d n u J N : ℕ) : ℕ :=
  43*byteCapacity n B d u J N+37+
    mulEnvelope B d n u J N+addEnvelope B d n u J N

def loopEnvelope (B d n u J N L : ℕ) : ℕ :=
  L*(quadraticEnvelope B d n u J N+accumulatorEnvelope B d n u J N+2)+1

def applyEnvelope (B d n u J N L keyLength : ℕ) : ℕ :=
  30*B*L+11*byteCapacity n B d u J N+2*keyLength+23+
    loopEnvelope B d n u J N L

theorem stepEnvelope_mono_right (B d n u J N a b : ℕ) (h : a ≤ b) :
    Product.stepEnvelope B d n u J N a ≤ Product.stepEnvelope B d n u J N b := by
  dsimp [Product.stepEnvelope]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem wordCost_le (B d n : ℕ) : ReadScalar.wordCost B d n ≤ wordEnvelope B d n := by
  have h := Nat.mul_le_mul_right (7*B+7) (Nat.sub_le d 1)
  dsimp [ReadScalar.wordCost,wordEnvelope]
  omega

theorem mulCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (a b : Stored p t (n:=n) (d:=d)) (ha : Bounded ctx vars a) (hb : Bounded ctx vars b) :
    mulCost ctx a b ≤ mulEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  let N := capacity vars ctx.u ctx.J
  have hout := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J a b ha.1 hb.1
  have ba := bounded_bytes ctx vars a ha
  have bb := bounded_bytes ctx vars b hb
  have bo := bounded_bytes ctx vars (mul ctx a b) (good_bounded ctx vars _ hout)
  have hw := Product.work_le p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J (N*N) a b []
    (fun x hx => (ha.1 x hx).1) (fun x hx => (hb.1 x hx).1)
    (by intro x hx; simp at hx) (by simpa using Nat.mul_le_mul ha.2 hb.2)
  have hstep := stepEnvelope_mono_right (baseWidth p t) d n ctx.u ctx.J (N*N)
    b.length N hb.2
  have hm := (Nat.mul_le_mul_left a.length (Nat.add_le_add_right hstep 2)).trans
    (Nat.mul_le_mul_right (Product.stepEnvelope (baseWidth p t) d n ctx.u ctx.J (N*N) N+2) ha.2)
  have hwork := hw.trans (Nat.add_le_add_right hm 1)
  dsimp only [mulCost,mulEnvelope,N] at *
  omega

theorem addCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (a b : Stored p t (n:=n) (d:=d)) (ha : Bounded ctx vars a) (hb : Good vars ctx.u ctx.J b) :
    addCost ctx a b ≤ addEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  let N := capacity vars ctx.u ctx.J
  have hbb := good_bounded ctx vars b hb
  have hout := add_good ctx.modulus ctx.cache vars ctx.u ctx.J a b ha.1 hb
  have ba := bounded_bytes ctx vars a ha
  have bb := bounded_bytes ctx vars b hbb
  have bo := bounded_bytes ctx vars (plus ctx a b) (good_bounded ctx vars _ hout)
  have hw := Normalize.work_le p t ctx.modulus ctx.cache Squarefree.encodeIndex
    (n+ctx.u+ctx.J) (2*N) a b (valid_keyBound vars ctx.u ctx.J a ha.1)
    (valid_keyBound vars ctx.u ctx.J b hb.1)
    (by have haN := ha.2; have hbN := hbb.2; dsimp [N]; omega)
  have hm := Nat.mul_le_mul_right
    (220*(2*N+1)*(n+ctx.u+ctx.J+d*baseWidth p t+1)+
      MomentsProgram.Dictionary.codeBranchBudget (baseWidth p t) d+2) ha.2
  have hwork := hw.trans (Nat.add_le_add_right hm 1)
  dsimp only [addCost,addEnvelope,N] at *
  omega

theorem quadraticCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (v : Triple (RingProgram.ScalarCode p t)) :
    quadraticCost ctx h v ≤
      quadraticEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  have hc := constant_good (d:=d) ctx.cache vars ctx.u ctx.J hu hJ v.c
  have hb := constant_good (d:=d) ctx.cache vars ctx.u ctx.J hu hJ v.b
  have ha := constant_good (d:=d) ctx.cache vars ctx.u ctx.J hu hJ v.a
  have hch := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J _ h hc.1 hh.1
  have hchb := add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ _ hch.1 hb
  have hchbh := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J _ h hchb.1 hh.1
  have b1 := mulCost_le ctx vars (constant ctx v.c) h (good_bounded ctx vars _ hc) hh
  have b2 := addCost_le ctx vars (mul ctx (constant ctx v.c) h) (constant ctx v.b)
    (good_bounded ctx vars _ hch) hb
  have b3 := mulCost_le ctx vars (plus ctx (mul ctx (constant ctx v.c) h) (constant ctx v.b)) h
    (good_bounded ctx vars _ hchb) hh
  have b4 := addCost_le ctx vars
    (mul ctx (plus ctx (mul ctx (constant ctx v.c) h) (constant ctx v.b)) h) (constant ctx v.a)
    (good_bounded ctx vars _ hchbh) ha
  have bw := wordCost_le (baseWidth p t) d n
  have bh := bounded_bytes ctx vars h hh
  dsimp only [quadraticCost,quadraticEnvelope]
  omega

theorem accumulatorCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (e a g : Stored p t (n:=n) (d:=d))
    (he : Good vars ctx.u ctx.J e) (ha : Bounded ctx vars a) (hg : Bounded ctx vars g) :
    accumulatorCost ctx e a g ≤
      accumulatorEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  have hag := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J a g ha.1 hg.1
  have hout := add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ e hag.1 he
  have bm := mulCost_le ctx vars a g ha hg
  have ba := addCost_le ctx vars (mul ctx a g) e (good_bounded ctx vars _ hag) he
  have be := bounded_bytes ctx vars e (good_bounded ctx vars e he)
  have baa := bounded_bytes ctx vars a ha
  have bg := bounded_bytes ctx vars g hg
  have bo := bounded_bytes ctx vars (plus ctx (mul ctx a g) e) (good_bounded ctx vars _ hout)
  dsimp only [accumulatorCost,accumulatorEnvelope]
  omega

theorem loopResult_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h g : Stored p t (n:=n) (d:=d))
    (hh : Valid vars ctx.u ctx.J h) (hg : Valid vars ctx.u ctx.J g)
    (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Stored p t (n:=n) (d:=d))
    (ha : Good vars ctx.u ctx.J a) :
    Good vars ctx.u ctx.J (loopResult ctx h g vs a) := by
  induction vs generalizing a with
  | nil => exact ha
  | cons v vs ih =>
    have he := triple_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J hu hJ h hh v
    have hm := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J a g ha.1 hg
    exact ih _ (add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ _ hm.1 he)

theorem loopCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h g : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (hg : Bounded ctx vars g)
    (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Stored p t (n:=n) (d:=d))
    (ha : Bounded ctx vars a) :
    loopCost ctx h g vs a ≤
      loopEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) vs.length := by
  induction vs generalizing a with
  | nil => simp [loopCost,loopEnvelope]
  | cons v vs ih =>
    let e := tripleStored p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J h v
    have he : Good vars ctx.u ctx.J e :=
      triple_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J hu hJ h hh.1 v
    have hm := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J a g ha.1 hg.1
    have hn := add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ e hm.1 he
    have br := ih (plus ctx (mul ctx a g) e) (good_bounded ctx vars _ hn)
    have bq := quadraticCost_le ctx vars hu hJ h hh v
    have ba := accumulatorCost_le ctx vars e a g he ha hg
    dsimp only [loopCost,loopEnvelope] at *
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    dsimp only [e] at *
    omega

theorem triplesTape_length {B : ℕ} (vs : List (Triple (Word B))) :
    (triplesTape vs).length=3*B*vs.length := by
  have h := congrArg List.length (triplesTape_reverse vs)
  simpa only [List.length_reverse,descendingTape_length] using h

theorem applyLoopCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h g : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (hg : Bounded ctx vars g)
    (vs : List (Triple (RingProgram.ScalarCode p t))) (key : List Bool) :
    applyLoopCost ctx h g vs key ≤
      applyEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) vs.length key.length := by
  have hn := good_nil (B:=baseWidth p t) (d:=d) vars ctx.u ctx.J
  have ho := loopResult_good ctx vars hu hJ h g hh.1 hg.1 vs.reverse [] hn
  have bo := bounded_bytes ctx vars (loopResult ctx h g vs.reverse []) (good_bounded ctx vars _ ho)
  have bg := bounded_bytes ctx vars g hg
  have bl := loopCost_le ctx vars hu hJ h g hh hg vs.reverse [] (good_bounded ctx vars _ hn)
  rw [List.length_reverse] at bl
  dsimp only [applyLoopCost,applyEnvelope]
  rw [triplesTape_length]
  nlinarith

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
