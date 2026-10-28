import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCofactorControl
import OAI.Algorithms.SubexponentialSAT.SubexpRecordFlatten

namespace OAI.Algorithms

/-!
# Fixed physical control for source-field inverse caches

The initial node source at 97 is a framed record list. The first phase removes
the framing. Subsequent loops consume copies of the packed node array and of
the packed negative-node array. No index multiplication occurs at runtime.

Final arrays are nodes97, inverses98, negatives100, and row-major differences103.
The unchanged scalar-service inputs are modulus66, reduction73, width74,
exponent91, minusOne92, and unit93. Stack104 is a charged copy of unit93 used
only for its length; it is cleared on return. Other working ports are empty.
-/

namespace SubexponentialSAT.SubexpFieldCacheControl

open BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open SubexpCRTCofactorControl

def flattenRegisters : Fin 5 ↪ Fin 8 :=
  ⟨Fin.castAdd 3, Fin.castAdd_injective _ _⟩

def flattenPorts : Fin 4 ↪ Fin 110 := ⟨![97, 94, 99, 107], by decide⟩

abbrev flatten : Cmd 8 110 :=
  .call (ProgramLinking.liftProgram SubexpRecordFlatten.program flattenRegisters flattenPorts)

abbrev copy (src dst : Fin 110) : Cmd 8 110 :=
  .call (copyProgram src dst 0 (0 : Fin 8) 1)

abbrev reverse (src : Fin 110) : Cmd 8 110 :=
  .call (reverseProgram src 107 108 (0 : Fin 8) 1)

abbrev emit (src dst : Fin 110) : Cmd 8 110 :=
  .call (transferProgram src dst (0 : Fin 8) 1)

abbrev peek (src : Fin 110) : Cmd 8 110 := .base (.atom (.peek src 0 1))

local infixr:60 " ;; " => Cmd.seq

/-- Every node first passes through actual powering, then actual negation.
Both outputs are accumulated in reverse bit order for one final reversal. -/
abbrev nodeIteration (negate power : Cmd 8 110) : Cmd 8 110 :=
  takeNode ;; copy 94 95 ;; power ;; clear 95 ;; negate ;;
    emit 96 98 ;; emit 95 100 ;; clear 94

abbrev nodePass (negate power : Cmd 8 110) : Cmd 8 110 :=
  copy 97 99 ;; peek 99 ;;
    .while 1 (nodeIteration negate power ;; peek 99) ;;
    reverse 98 ;; reverse 100

/-- One inner iteration uses a copied positive node and a negative node read
from the array. The addition service consumes95 and leaves its result in70. -/
abbrev pairIteration (add power : Cmd 8 110) : Cmd 8 110 :=
  takeWord 104 107 108 99 95 0 1 ;; copy 94 70 ;; add ;;
    move 70 95 ;; power ;; clear 95 ;; emit 96 103

abbrev pairRow (add power : Cmd 8 110) : Cmd 8 110 :=
  takeWord 104 107 108 106 94 0 1 ;; copy 100 99 ;; peek 99 ;;
    .while 1 (pairIteration add power ;; peek 99) ;; clear 94

abbrev pairPass (add power : Cmd 8 110) : Cmd 8 110 :=
  copy 97 106 ;; peek 106 ;; .while 1 (pairRow add power ;; peek 106) ;; reverse 103

abbrev command (negate add power : Cmd 8 110) : Cmd 8 110 :=
  flatten ;; copy 93 104 ;; nodePass negate power ;; pairPass add power ;; clear 104

abbrev program (negate add power : Cmd 8 110) :=
  compiled (command negate add power) 97 103

def extra (j : Fin 110) : Prop := j = 97 ∨ j = 100 ∨ j = 103 ∨ j = 106

theorem store_extra (frame : Fin 110 → List Bool) (w : Words) (j : Fin 110)
    (hj : extra j) : store frame w j = frame j := by
  rcases hj with rfl | rfl | rfl | rfl <;> rfl

theorem update_store_extra (frame : Fin 110 → List Bool) (w : Words)
    (j : Fin 110) (bits : List Bool) (hj : extra j) :
    Function.update (store frame w) j bits = store (Function.update frame j bits) w := by
  funext i
  by_cases hi : i = j
  · subst i
    rw [Function.update_same, store_extra _ _ _ hj, Function.update_same]
  · rw [Function.update_of_ne hi]
    simp only [store, Function.update_of_ne hi]

/-- The elementary accumulator operation reverses each emitted block. This
identity certifies why one final reversal gives the exact original order. -/
theorem reverse_accumulate (blocks : List (List Bool)) (acc : List Bool) :
    blocks.foldl (fun xs block => block.reverse ++ xs) acc = blocks.flatten.reverse ++ acc :=
  SubexpRecordFlatten.fold_reverse blocks acc

def rowMajor {A B C : Type*} (f : A → B → C) (xs : List A) (ys : List B) : List C :=
  xs.flatMap fun x => ys.map (f x)

@[simp] theorem rowMajor_length {A B C : Type*} (f : A → B → C)
    (xs : List A) (ys : List B) : (rowMajor f xs ys).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [rowMajor]
  | cons x xs ih => simp [rowMajor, Nat.succ_mul, Nat.add_comm]

end SubexponentialSAT.SubexpFieldCacheControl

end OAI.Algorithms
