import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterInput
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterCofactor
import OAI.Algorithms.SubexponentialSAT.SubexpCRTWeightedMachine

namespace OAI.Algorithms

/-! The outer controller constructs the exact native cofactor input by copying
its represented exponent, unit and omitted-node stream. -/

namespace SubexponentialSAT.SubexpCRTOuterCofactorView

attribute [local simp] Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpCRTOuterProgram
open SubexpQuarticFlatMul (flat)

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := SubexpPolynomialPowerProgram.Coefficient p (D + 1)
abbrev Poly := SubexpPolynomialPowerProgram.FixedPolynomial p (D + 1) D

def words (t one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
    (width binaryD : List Bool) : SubexpCRTCofactorControl.Words where
  modulus := M.bits
  reduction := flat t
  width := width
  exponent := binaryD
  minusOne := minusOne.val
  unit := flat one
  blockWidth := List.replicate (4 * baseWidth p (D + 1)) false
  stream := []
  accumulator := []

variable {Q : ℕ} (t one : Coeff p D) (minusOne : Word (baseWidth p (D + 1)))
  (width exponent binaryD : List Bool) (nodes : Fin Q → Coeff p D)
  (jets : Fin Q → Poly p D) (processed remaining : List (Fin Q))
  (current : Fin Q) (acc : Coeff p D)

local notation "s" => SubexpCRTOuterInput.loaded p D M t one minusOne width exponent binaryD
  nodes jets processed remaining current acc

def input (regs : Fin 16 → Bool) (correction : List Bool) : Data :=
  ⟨regs, Function.update s 244 correction⟩

omit [Fact p.Prime] in
theorem clean (regs : Fin 16 → Bool) (correction : List Bool) :
    ∀ j ∈ SubexpCRTOuterCofactor.cleanPorts,
      (input p D M t one minusOne width exponent binaryD nodes jets processed remaining current acc
        regs correction).stacks j = [] := by
  intro j hj
  simp only [SubexpCRTOuterCofactor.cleanPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [input, SubexpCRTOuterInput.loaded, SubexpCRTOuterInput.data,
      SubexpCRTOuterInput.store, SubexpCRTOuterInput.baseContext,
      SubexpCRTCanonicalInput.store, initializedStacks, sweepStore,
      SubexpQuarticFlatMul.bankStore]

omit [Fact p.Prime] in
/-- No readiness or arithmetic oracle is assumed: every port is read from
its explicit represented input and the six executed copy operations. -/
theorem prepared_view (hw : width.length = baseWidth p (D + 1))
    (regs : Fin 16 → Bool) (correction : List Bool) :
    ∀ j, (SubexpCRTOuterCofactor.prepared
      (input p D M t one minusOne width exponent binaryD nodes jets processed remaining current acc
        regs correction)).stacks (scalarPorts j) =
      SubexpCRTCofactorControl.store (fun j => s (scalarPorts j))
        (SubexpCRTCofactorLoop.initialWords flat (words p D M t one minusOne width binaryD)
          ((remaining ++ processed).map nodes)) j := by
  intro j
  refine Fin.addCases (m := 77) (n := 33) (fun i => ?_) (fun i => ?_) j
  · have hn (k : Fin 320) (hk : 205 ≤ k.val) : scalarPorts (i.castAdd 33) ≠ k := by
      intro heq
      have hv := congrArg Fin.val heq
      change 128 + i.val = k.val at hv
      have hi := i.isLt
      omega
    have hsame : (SubexpCRTOuterCofactor.prepared
        (input p D M t one minusOne width exponent binaryD nodes jets processed remaining current acc
          regs correction)).stacks (scalarPorts (i.castAdd 33)) = s (scalarPorts (i.castAdd 33)) := by
      simp [SubexpCRTOuterCofactor.prepared_stacks, input,
        hn 219 (by decide), hn 220 (by decide), hn 221 (by decide), hn 232 (by decide),
        hn 227 (by decide), hn 244 (by decide)]
    rw [hsame]
    have hh := congrFun (SubexpCRTOuterInput.loaded_local_store p D M t one minusOne width exponent
      binaryD nodes jets hw processed remaining current acc (fun _ => false))
      (SubexpConvolutionPair.highPort i)
    change s (scalarPorts (i.castAdd 33)) = _ at hh
    rw [hh, SubexpCRTCanonicalInput.canonical, SubexpCRTCanonicalInput.store_high]
    by_cases h70 : i = 70
    · subst i
      simp [words, SubexpCRTCofactorControl.store, SubexpCRTCofactorControl.nativeStore,
        SubexpCRTCofactorLoop.initialWords, SubexpQuarticFlatMul.bankStore]
    by_cases h71 : i = 71
    · subst i
      simp [words, SubexpCRTCofactorControl.store, SubexpCRTCofactorControl.nativeStore,
        SubexpCRTCofactorLoop.initialWords, SubexpQuarticFlatMul.bankStore]
    simp [words, SubexpCRTCofactorControl.store, SubexpCRTCofactorControl.nativeStore,
      SubexpCRTCofactorLoop.initialWords, SubexpCRTCanonicalInput.context,
      i.isLt, h70, h71,
      SubexpCRTWeightedMachine.encode_eq_flat]
  · rw [SubexpCRTOuterCofactor.prepared_stacks]
    have hscalar (k : Fin 110) : scalarPorts k =
        (⟨128 + k.val, by omega⟩ : Fin 320) := rfl
    have hport : scalarPorts (Fin.natAdd 77 i) =
        (⟨205 + i.val, by omega⟩ : Fin 320) := by
      apply Fin.ext
      change 128 + (77 + i.val) = 205 + i.val
      omega
    rw [hport]
    fin_cases i <;>
      simp [input, words, SubexpCRTOuterInput.loaded, SubexpCRTOuterInput.data,
        SubexpCRTOuterInput.store, SubexpCRTOuterInput.baseContext,
        SubexpCRTCanonicalInput.store, initializedStacks, sweepStore, loadedReady, loadedWords,
        readyWords, hscalar, SubexpCRTCofactorControl.store,
        SubexpCRTCofactorLoop.initialWords,
        SubexpQuarticFlatMul.bankStore, Fin.coe_ofNat_eq_mod,
        List.flatMap_append, List.flatMap_map, SubexpCRTWeightedMachine.encode_eq_flat, hw]

/-- A common polynomial cap for the actual cofactor command. The exponent
word comes from the checked unary-length conversion, so both its value and
its length are bounded by D. -/
def uniformBudget (B D Q : ℕ) : ℕ :=
  SubexpCRTCofactorMachine.polynomialBound (B + D + Q) +
    9 * D + 105 * B + 28 * Q * B + 48

omit [Fact p.Prime] in
theorem budget_le (hw : width.length = baseWidth p (D + 1))
    (he : BinaryArithmetic.toNat binaryD = D) (hl : binaryD.length ≤ D)
    (hfull : List.finRange Q = processed.reverse ++ current :: remaining)
    (regs : Fin 16 → Bool) (correction : List Bool) :
    SubexpCRTOuterCofactor.budget (baseWidth p (D + 1)) binaryD
      ((remaining ++ processed).map nodes).length
      (input p D M t one minusOne width exponent binaryD nodes jets processed remaining current acc
        regs correction) ≤ uniformBudget (baseWidth p (D + 1)) D Q := by
  have hc : remaining.length + processed.length ≤ Q := by
    have h := congrArg List.length hfull
    simp only [List.length_finRange, List.length_append, List.length_reverse,
      List.length_cons] at h
    omega
  have hm := SubexpCRTCofactorMachine.runtimeBound_le (baseWidth p (D + 1)) binaryD
    ((remaining ++ processed).map nodes).length (baseWidth p (D + 1) + D + Q)
    (by omega) (by omega) (by omega) (by simp only [List.length_map, List.length_append]; omega)
  simp only [List.length_map, List.length_append] at hm
  have hrest := flatMap_length_of_width (fun i => SubexpFlatAdd.encode (nodes i))
    (4 * baseWidth p (D + 1)) (fun _ => SubexpFlatAdd.encode_length _) remaining
  have hdone := flatMap_length_of_width (fun i => SubexpFlatAdd.encode (nodes i))
    (4 * baseWidth p (D + 1)) (fun _ => SubexpFlatAdd.encode_length _) processed
  simp [SubexpCRTOuterCofactor.budget, SubexpCRTOuterCofactor.prepareBudget,
    input, SubexpCRTOuterInput.loaded, SubexpCRTOuterInput.data,
    SubexpCRTOuterInput.store, SubexpCRTOuterInput.baseContext,
    SubexpCRTCanonicalInput.store, initializedStacks, sweepStore, loadedReady, loadedWords,
    readyWords, SubexpQuarticFlatMul.bankStore, hw, hrest, hdone, uniformBudget,
    SubexpFlatAdd.encode_length, minusOne.property]
  nlinarith [Nat.mul_le_mul_right (baseWidth p (D + 1)) hc]

end SubexponentialSAT.SubexpCRTOuterCofactorView

end OAI.Algorithms
