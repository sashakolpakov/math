import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramMultiplierKernel

namespace OAI.Algorithms

/-! The setup charge includes scaling by cached minus one, normalized cubic
arithmetic, construction of the U key, and the physical key-map loop. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps Multiplier

variable {p t n d : ℕ} [Fact p.Prime]

theorem scaled_valid (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h : Stored p t (n:=n) (d:=d)) (hh : Valid vars ctx.u ctx.J h) :
    Valid vars ctx.u ctx.J
      (Squarefree.ScaleProgram.scaled p t ctx.modulus ctx.cache ctx.table minus h) := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact hh b hb

theorem complemented_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Valid vars ctx.u ctx.J h) (ho : Good vars ctx.u ctx.J one) :
    Good vars ctx.u ctx.J (complemented ctx minus h one) :=
  add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ one (scaled_valid ctx vars minus h hh) ho

theorem cubic_good (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Valid vars ctx.u ctx.J h) (ho : Good vars ctx.u ctx.J one) :
    Good vars ctx.u ctx.J (cubic ctx minus h one) := by
  have ha := complemented_good ctx vars minus h one hh ho
  have hb := add_good ctx.modulus ctx.cache vars ctx.u ctx.J _ one ha.1 ho
  have hq := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J _ _ hb.1 ha.1
  exact mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J _ h hq.1 hh

omit [Fact (Nat.Prime p)] in
theorem shiftForward_eq_keptJoin (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (xs : Stored p t (n:=n) (d:=d)) :
    shiftForward a u J xs=Product.keptJoin a u J xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b,c⟩
    simp only [shiftForward,Product.keptJoin,ih]

theorem prepared_bounded (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Valid vars ctx.u ctx.J h) (ho : Good vars ctx.u ctx.J one) :
    Bounded ctx vars (prepared ctx minus h one) := by
  have hc := cubic_good ctx vars minus h one hh ho
  have hv := Product.keptJoin_valid vars ctx.u ctx.J (uKey n) (cubic ctx minus h one)
    (by simp [uKey,Squarefree.Index.Valid]) hc.1
  constructor
  · intro a ha
    apply hv a
    simpa only [prepared,shifted,List.mem_reverse,shiftForward_eq_keptJoin] using ha
  · have hl := Product.keptJoin_length (uKey n) ctx.u ctx.J (cubic ctx minus h one)
    simpa only [prepared,shifted,List.length_reverse,shiftForward_eq_keptJoin] using
      hl.trans (length_le_capacity vars ctx.u ctx.J _ hc)

def scaleStepEnvelope (B d n u J : ℕ) : ℕ :=
  40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+22*(n+u+J)+57

def normalizeStepEnvelope (B d n u J N : ℕ) : ℕ :=
  220*(2*N+1)*(n+u+J+d*B+1)+MomentsProgram.Dictionary.codeBranchBudget B d+2

def complementEnvelope (B d n u J N : ℕ) : ℕ :=
  52*byteCapacity n B d u J N+18*(d*B)+9*d+
    N*scaleStepEnvelope B d n u J+N*normalizeStepEnvelope B d n u J N+80

def arithmeticEnvelope (B d n u J N : ℕ) : ℕ :=
  46*byteCapacity n B d u J N+36+complementEnvelope B d n u J N+
    addEnvelope B d n u J N+2*mulEnvelope B d n u J N

def prepareEnvelope (B d n u J N : ℕ) : ℕ :=
  arithmeticEnvelope B d n u J N+20*n+53+N*(120*(n+u+J+d*B+3)+2)

theorem complementCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (ho : Good vars ctx.u ctx.J one) :
    complementCost ctx minus h one ≤
      complementEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  let N := capacity vars ctx.u ctx.J
  let scaled := Squarefree.ScaleProgram.scaled p t ctx.modulus ctx.cache ctx.table minus h
  have hs : Valid vars ctx.u ctx.J scaled := scaled_valid ctx vars minus h hh.1
  have hsl : scaled.length=h.length := by simp [scaled,Squarefree.ScaleProgram.scaled]
  have hone := good_bounded ctx vars one ho
  have hc := complemented_good ctx vars minus h one hh.1 ho
  have bh := bounded_bytes ctx vars h hh
  have bo := bounded_bytes ctx vars one hone
  have bc := bounded_bytes ctx vars _ (good_bounded ctx vars _ hc)
  have bs := Squarefree.ScaleProgram.budget_le Squarefree.encodeIndex h (n+ctx.u+ctx.J)
    (valid_keyBound vars ctx.u ctx.J h hh.1)
  have bs' := Nat.mul_le_mul_right (scaleStepEnvelope (baseWidth p t) d n ctx.u ctx.J) hh.2
  have bn := Normalize.work_le p t ctx.modulus ctx.cache Squarefree.encodeIndex
    (n+ctx.u+ctx.J) (2*N) scaled one (valid_keyBound vars ctx.u ctx.J scaled hs)
    (valid_keyBound vars ctx.u ctx.J one ho.1)
    (by rw [hsl]; have hhN := hh.2; have hoN := hone.2; dsimp [N]; omega)
  rw [hsl] at bn
  have bn' := Nat.mul_le_mul_right
    (normalizeStepEnvelope (baseWidth p t) d n ctx.u ctx.J N) hh.2
  dsimp only [complementCost,complementEnvelope,scaleStepEnvelope,normalizeStepEnvelope,N,scaled] at *
  rw [RingProgram.flat_length]
  omega

theorem arithmeticCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (ho : Good vars ctx.u ctx.J one) :
    arithmeticCost ctx minus h one ≤
      arithmeticEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  let a := complemented ctx minus h one
  let b := plus ctx a one
  have ha : Good vars ctx.u ctx.J a := complemented_good ctx vars minus h one hh.1 ho
  have hb : Good vars ctx.u ctx.J b := add_good ctx.modulus ctx.cache vars ctx.u ctx.J a one ha.1 ho
  have hq := mul_good ctx.modulus ctx.cache ctx.table vars ctx.u ctx.J b a hb.1 ha.1
  have bh := bounded_bytes ctx vars h hh
  have ba := bounded_bytes ctx vars a (good_bounded ctx vars a ha)
  have bo := bounded_bytes ctx vars one (good_bounded ctx vars one ho)
  have c1 := complementCost_le ctx vars minus h one hh ho
  have c2 := addCost_le ctx vars a one (good_bounded ctx vars a ha) ho
  have c3 := mulCost_le ctx vars b a (good_bounded ctx vars b hb) (good_bounded ctx vars a ha)
  have c4 := mulCost_le ctx vars (mul ctx b a) h (good_bounded ctx vars _ hq) hh
  dsimp only [arithmeticCost,arithmeticEnvelope,a,b] at *
  omega

theorem prepareCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (ho : Good vars ctx.u ctx.J one) :
    prepareCost ctx minus h one ≤
      prepareEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  have hc := cubic_good ctx vars minus h one hh.1 ho
  have hl := length_le_capacity vars ctx.u ctx.J _ hc
  have hb := uKey_budget_le (C:=d*baseWidth p t) (byteEntries (cubic ctx minus h one))
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact (hc.1 b hb).1)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2))
  simp only [byteEntries,List.length_map] at hb
  have hm := Nat.mul_le_mul_right (120*(n+ctx.u+ctx.J+d*baseWidth p t+3)+2) hl
  have ha := arithmeticCost_le ctx vars minus h one hh ho
  dsimp only [prepareCost,prepareEnvelope,byteEntries]
  omega

def totalEnvelope (B d n u J N L : ℕ) : ℕ :=
  prepareEnvelope B d n u J N+applyEnvelope B d n u J N L (n+3)+1

theorem totalCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (ho : Good vars ctx.u ctx.J one)
    (vs : List (Triple (RingProgram.ScalarCode p t))) :
    prepareCost ctx minus h one+
      applyLoopCost ctx h (prepared ctx minus h one) vs (Squarefree.encodeIndex (uKey n))+1 ≤
      totalEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) vs.length := by
  have hp := prepareCost_le ctx vars minus h one hh ho
  have hg := prepared_bounded ctx vars minus h one hh.1 ho
  have ha := applyLoopCost_le ctx vars hu hJ h (prepared ctx minus h one) hh hg vs
    (Squarefree.encodeIndex (uKey n))
  have hk : (Squarefree.encodeIndex (uKey n)).length=n+3 := by simp [uKey_encode]
  rw [hk] at ha
  exact Nat.add_le_add_right (Nat.add_le_add hp ha) 1

/-- The real degree-two coefficient table has exactly t digits and 3*B*t
bits, rather than a table indexed by Boolean assignments. -/
theorem totalCost_coefficient_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (ho : Good vars ctx.u ctx.J one)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    prepareCost ctx minus h one+
      applyLoopCost ctx h (prepared ctx minus h one) (List.ofFn (coefficientTriple t code))
        (Squarefree.encodeIndex (uKey n))+1 ≤
      totalEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) t := by
  simpa only [List.length_ofFn] using
    totalCost_le ctx vars hu hJ minus h one hh ho (List.ofFn (coefficientTriple t code))

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
