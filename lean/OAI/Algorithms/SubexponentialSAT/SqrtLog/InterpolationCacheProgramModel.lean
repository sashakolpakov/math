import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramNativeInverse
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgramModel

namespace OAI.Algorithms

/-! Values computed by the physical interpolation-cache producer. Every
entry is a typed output of an executable ring program. The uniform inverse
routine has an explicit zero-diagonal interpretation. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT
open scoped BigOperators

abbrev Coeff (t d : ℕ) := RingProgram.Code (RingProgram.ScalarCode 3 t) d

def inverseValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne x : Coeff t d) : Coeff t d :=
  CRTLocalProgram.NativeInverse.value t a M cache x
    (RingProgram.modelProgram t a M cache).zeroRun.1 minusOne

def negativeValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne x : Coeff t d) : Coeff t d :=
  ((RingProgram.modelProgram t a M cache).mulRun x minusOne).1

def differenceValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne x y : Coeff t d) : Coeff t d :=
  CRTLocalProgram.NativeInverse.value t a M cache x y minusOne

def inverseList (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :=
  xs.map (inverseValue t a M cache minusOne)

def negativeList (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :=
  xs.map (negativeValue t a M cache minusOne)

def differenceRows (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :=
  xs.map fun x => xs.map (differenceValue t a M cache minusOne x)

theorem negativeValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne x : Coeff t d)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1) :
    (RingProgram.modelRing t ht hd a M cache).decode (negativeValue t a M cache minusOne x) =
      -(RingProgram.modelRing t ht hd a M cache).decode x := by
  let ops := RingProgram.modelRing t ht hd a M cache
  change ops.decode (ops.mulRun x minusOne).1 = -ops.decode x
  rw [ops.mul_correct,hm]
  exact mul_neg_one (ops.decode x)

theorem inverseValue_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne x : Coeff t d)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (hx : a.rho t ht ((RingProgram.modelRing t ht hd a M cache).decode x) ≠ 0) :
    (RingProgram.modelRing t ht hd a M cache).decode (inverseValue t a M cache minusOne x) *
      (RingProgram.modelRing t ht hd a M cache).decode x = 1 := by
  let ops := RingProgram.modelRing t ht hd a M cache
  have hz : ops.decode ops.zeroRun.1=0 := ops.zero_correct
  have hz' : (RingProgram.modelRing t ht hd a M cache).decode ops.zeroRun.1=0 := hz
  have h := CRTLocalProgram.NativeInverse.value_correct t ht hd a M cache x
    ops.zeroRun.1 minusOne hm (by simpa only [hz',map_zero] using hx)
  rw [hz',sub_zero] at h
  exact h

theorem differenceValue_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne x y : Coeff t d)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (hxy : a.rho t ht ((RingProgram.modelRing t ht hd a M cache).decode x) ≠
      a.rho t ht ((RingProgram.modelRing t ht hd a M cache).decode y)) :
    (RingProgram.modelRing t ht hd a M cache).decode (differenceValue t a M cache minusOne x y) *
      ((RingProgram.modelRing t ht hd a M cache).decode x -
        (RingProgram.modelRing t ht hd a M cache).decode y) = 1 :=
  CRTLocalProgram.NativeInverse.value_correct t ht hd a M cache x y minusOne hm hxy

/-- The actual total inverse computation returns zero on equal nodes. It
therefore implements the required diagonal convention without a branch. -/
theorem differenceValue_diagonal (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne x : Coeff t d)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1) :
    (RingProgram.modelRing t ht hd a M cache).decode (differenceValue t a M cache minusOne x x)=0 := by
  let ops := RingProgram.modelRing t ht hd a M cache
  let mulOp := fun x y => (ops.mulRun x y).1
  let addOp := fun x y => (ops.addRun x y).1
  have hdelta : ops.decode (CRTLocalProgram.differenceValue mulOp addOp x x minusOne)=0 := by
    rw [CRTLocalProgram.differenceValue_decode ops.decode mulOp addOp ops.mul_correct
      ops.add_correct x x minusOne hm,sub_self]
  have hpow : 3^d-2 ≠ 0 := by
    have hp : 3^1 ≤ 3^d := Nat.pow_le_pow_right (by decide) hd
    norm_num at hp
    omega
  change ops.decode (CRTLocalProgram.inverseValue mulOp addOp ops.zeroRun.1 ops.oneRun.1
    minusOne (CRTLocalProgram.differenceValue mulOp addOp x x minusOne) (3^d-2) t)=0
  rw [CRTLocalProgram.inverseValue_decode ops.decode mulOp addOp ops.mul_correct
    ops.add_correct _ _ _ _ ops.zero_correct ops.one_correct hm,
    SubexpResidueInverse.inverseWithCost_value,hdelta]
  simp [NilpotentDefect.geometricInverse,zero_pow hpow]

theorem node_inverse_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne : Coeff t d)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (Q : ℕ) (hQ : Q < 3^d) (i : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode
      (inverseValue t a M cache minusOne (RingNodeProgram.nodeCode t d (i.val+1))) *
      a.node t Q ht hQ i=1 := by
  rw [← RingNodeProgram.nodeCode_decode t ht hd a M cache Q hQ i]
  apply inverseValue_correct t ht hd a M cache minusOne _ hm
  exact RingNodeProgram.generated_residue_ne_zero t ht hd a M cache Q hQ i

theorem nodes_difference_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne : Coeff t d)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (Q : ℕ) (hQ : Q < 3^d) (i j : Fin Q) (hij : i≠j) :
    (RingProgram.modelRing t ht hd a M cache).decode
      (differenceValue t a M cache minusOne (RingNodeProgram.nodeCode t d (i.val+1))
        (RingNodeProgram.nodeCode t d (j.val+1))) *
      (a.node t Q ht hQ i-a.node t Q ht hQ j)=1 := by
  rw [← RingNodeProgram.nodeCode_decode t ht hd a M cache Q hQ i,
    ← RingNodeProgram.nodeCode_decode t ht hd a M cache Q hQ j]
  apply differenceValue_correct t ht hd a M cache minusOne _ _ hm
  exact fun he => hij (RingNodeProgram.generated_residue_injective t ht hd a M cache Q hQ he)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
