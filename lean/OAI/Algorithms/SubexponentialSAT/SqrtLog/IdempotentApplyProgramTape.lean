import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramWords

namespace OAI.Algorithms

/-! Byte order for descending Horner application. A single whole-tape reversal
puts the last digit first and each digit's coefficients in c,b,a order. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open SubexpQuarticRing

def tripleTape {B : ℕ} (v : Triple (Word B)) : List Bool :=
  v.a.val ++ v.b.val ++ v.c.val

def triplesTape {B : ℕ} (vs : List (Triple (Word B))) : List Bool :=
  (vs.map tripleTape).flatten

def descendingTape {B : ℕ} (vs : List (Triple (Word B))) : List Bool :=
  (vs.map fun v => v.c.val.reverse ++ v.b.val.reverse ++ v.a.val.reverse).flatten

theorem triplesTape_reverse {B : ℕ} (vs : List (Triple (Word B))) :
    (triplesTape vs).reverse=descendingTape vs.reverse := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp [triplesTape,descendingTape,tripleTape,List.reverse_cons,List.map_append,
      List.flatten_append,List.reverse_append]
    simpa [triplesTape,descendingTape,List.map_reverse,List.append_assoc] using ih

theorem coefficient_tape {B t : ℕ} (code : RingProgram.Code (Word B) (3*t)) :
    RingProgram.flat code=triplesTape (List.ofFn (coefficientTriple t code)) := by
  unfold RingProgram.flat
  rw [List.ofFn_mul']
  simp [triplesTape,tripleTape,coefficientTriple,IdempotentProgram.digitIndex,List.map_ofFn,List.flatten_flatten,List.ofFn_succ,Function.comp_def]

theorem coefficient_tape_reverse {B t : ℕ} (code : RingProgram.Code (Word B) (3*t)) :
    (RingProgram.flat code).reverse=
      descendingTape (List.ofFn (coefficientTriple t code)).reverse := by
  rw [coefficient_tape,triplesTape_reverse]


theorem descendingTape_cons {B : ℕ} (v : Triple (Word B)) (vs : List (Triple (Word B))) :
    descendingTape (v::vs)=v.c.val.reverse++(v.b.val.reverse++(v.a.val.reverse++descendingTape vs)) := by
  simp [descendingTape,List.append_assoc]

theorem descendingTape_length {B : ℕ} (vs : List (Triple (Word B))) :
    (descendingTape vs).length=3*B*vs.length := by
  induction vs with
  | nil => simp [descendingTape]
  | cons v vs ih =>
    rw [descendingTape_cons]
    simp only [List.length_append,List.length_reverse, v.a.property,v.b.property,v.c.property,List.length_cons,ih,Nat.mul_add,Nat.mul_one]
    omega

theorem descendingTape_cons_ne_nil {B : ℕ} (hB : 0 < B)
    (v : Triple (Word B)) (vs : List (Triple (Word B))) : descendingTape (v::vs)≠[] := by
  intro h
  have he:=congrArg List.length h
  rw [descendingTape_length] at he
  simp only [List.length_cons,List.length_nil] at he
  nlinarith

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
