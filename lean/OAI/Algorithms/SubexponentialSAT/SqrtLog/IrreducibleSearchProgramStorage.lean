import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramScalar
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms

namespace OAI.Algorithms

/-! Paid preserving access to the search's coefficient arrays. The address
is a unary input stack, never a program parameter; every access uses the
same 38-label program. The source and scalar width are restored. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

def coefficientWord (a : IrreducibleSearch.F) : List Bool :=
  (SubexpEnumerationPayload.scalarCode 3).block a

def coefficientArray (as : List IrreducibleSearch.F) : List Bool :=
  StackEncoding.encodeDataStack (SubexpEnumerationPayload.scalarCode 3) as

@[simp] theorem coefficientWord_length (a : IrreducibleSearch.F) :
    (coefficientWord a).length = 2 := by
  have h := SubexpEnumerationPayload.scalarBits_length a
  have hw : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
    have hl : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    simp only [SubexpEnumerationPayload.scalarWidth, hl]
  simpa only [coefficientWord, SubexpEnumerationPayload.scalarCode, hw] using h

@[simp] theorem coefficientArray_nil : coefficientArray [] = [] := rfl

@[simp] theorem coefficientArray_cons (a : IrreducibleSearch.F)
    (as : List IrreducibleSearch.F) :
    coefficientArray (a :: as) = coefficientWord a ++ coefficientArray as := rfl

@[simp] theorem coefficientArray_append (as bs : List IrreducibleSearch.F) :
    coefficientArray (as ++ bs) = coefficientArray as ++ coefficientArray bs :=
  StackEncoding.encodeDataStack_append _ _ _

theorem coefficientArray_flatten (as : List IrreducibleSearch.F) :
    coefficientArray as = (as.map coefficientWord).flatten := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [coefficientArray_cons, List.map_cons, List.flatten_cons, ih]

@[simp] theorem coefficientArray_length (as : List IrreducibleSearch.F) :
    (coefficientArray as).length = 2 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]; omega

theorem coefficientArray_ofFn {d : ℕ} (a : Fin d → IrreducibleSearch.F) :
    coefficientArray (List.ofFn a) =
      SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) a := rfl

def coefficientReadProgram : Program 2 8 38 := ArrayUpdatePrograms.readProgram 0 1

theorem coefficientRead_trace (before after : List IrreducibleSearch.F)
    (a : IrreducibleSearch.F) (index : List Bool)
    (regs : Fin 2 → Bool) (stk : Fin 8 → List Bool)
    (harray : stk 0 = coefficientArray (before ++ a :: after))
    (hindex : stk 2 = index) (hlen : index.length = before.length)
    (hwidth : stk 3 = [false, false])
    (h4 : stk 4 = []) (h5 : stk 5 = []) (h6 : stk 6 = []) (h7 : stk 7 = []) :
    Trace coefficientReadProgram (38 * before.length + 46)
      ⟨some coefficientReadProgram.entry, regs, stk⟩
      ⟨none, readRegs regs 0 1 none, ArrayUpdatePrograms.readStacks (coefficientWord a) stk⟩ := by
  have he := ArrayUpdatePrograms.readProgram_trace (0 : Fin 2) 1 (by decide)
    (before.map coefficientWord) (coefficientWord a) (coefficientArray after)
    [false, false] index regs stk
    (by rw [harray, coefficientArray_append, coefficientArray_cons, coefficientArray_flatten before])
    hwidth hindex (by simpa using hlen)
    (by
      intro row hr
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
      simp)
    (by simp) h4 h5 h6 h7
  have htime :
      (before.map coefficientWord).length * (14 * [false, false].length + 10) +
          15 * [false, false].length + 16 =
        38 * before.length + 46 := by
    simp only [List.length_map, List.length_cons, List.length_nil]
    omega
  rw [htime] at he
  exact he

theorem coefficientRead_result (a : IrreducibleSearch.F) (stk : Fin 8 → List Bool) :
    ArrayUpdatePrograms.readStacks (coefficientWord a) stk 0 = stk 0 ∧
    ArrayUpdatePrograms.readStacks (coefficientWord a) stk 1 = coefficientWord a ++ stk 1 ∧
    ArrayUpdatePrograms.readStacks (coefficientWord a) stk 2 = [] := by
  simp

theorem coefficientRead_primitive (before after : List IrreducibleSearch.F)
    (a : IrreducibleSearch.F) (index : List Bool)
    (regs : Fin 2 → Bool) (stk : Fin 8 → List Bool)
    (harray : stk 0 = coefficientArray (before ++ a :: after))
    (hindex : stk 2 = index) (hlen : index.length = before.length)
    (hwidth : stk 3 = [false, false])
    (h4 : stk 4 = []) (h5 : stk 5 = []) (h6 : stk 6 = []) (h7 : stk 7 = []) :
    Computation.RunsIn (primitive coefficientReadProgram).step
      (primitiveOverhead coefficientReadProgram * (38 * before.length + 46))
      (primitiveCfg coefficientReadProgram ⟨some coefficientReadProgram.entry, regs, stk⟩)
      (primitiveCfg coefficientReadProgram
        ⟨none, readRegs regs 0 1 none, ArrayUpdatePrograms.readStacks (coefficientWord a) stk⟩) := by
  apply BitProgram.primitive_execution
  exact ⟨_, Nat.le_refl _, coefficientRead_trace before after a index regs stk
    harray hindex hlen hwidth h4 h5 h6 h7⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
