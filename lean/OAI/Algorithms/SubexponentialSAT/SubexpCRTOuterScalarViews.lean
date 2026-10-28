import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterInput
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterNeg
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterAccumulate

namespace OAI.Algorithms

/-!
# Physical scalar-service views of the loaded outer CRT store

These are equalities of the actual represented stack store. They add no
arithmetic callback or execution assumption. The final lemmas preserve all
three service views under writes to the outer loop's four result ports.
-/

namespace SubexponentialSAT.SubexpCRTOuterScalarViews

open SubexpLiftRing SubexpQuarticRing SubexpCRTOuterProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The weighted service starts with only its arithmetic metadata installed. -/
def weightedWords (modulus reduction width : List Bool) : SubexpCRTCofactorControl.Words where
  modulus := modulus
  reduction := reduction
  width := width
  exponent := []
  minusOne := []
  unit := []
  blockWidth := []
  stream := []
  accumulator := []

def nativePort (i : Fin 77) : Fin 320 := ⟨128 + i.val, by omega⟩

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))
  {Q : ℕ} (t one : SubexpCRTOuterInput.Coeff p D)
  (minusOne : Word (baseWidth p (D + 1))) (width exponent binaryD : List Bool)
  (nodes : Fin Q → SubexpCRTOuterInput.Coeff p D)
  (jets : Fin Q → SubexpCRTOuterInput.Poly p D)
  (processed remaining : List (Fin Q)) (current : Fin Q)
  (acc : SubexpCRTOuterInput.Coeff p D)

local notation "L" => SubexpCRTOuterInput.loaded p D M t one minusOne width exponent binaryD
  nodes jets processed remaining current acc

omit [Fact p.Prime] in
/-- Loading changes only five of the original 256 local coordinates. -/
theorem loaded_base (j : Fin 320) (hj : j.val < 256)
    (h104 : j ≠ 104) (h213 : j ≠ 213) (h214 : j ≠ 214)
    (h216 : j ≠ 216) (h225 : j ≠ 225) :
    L j = SubexpCRTCanonicalInput.store
      (SubexpCRTOuterInput.baseContext p D M t one minusOne width exponent) ⟨j.val, hj⟩ := by
  have hn (k : Fin 320) (hk : 256 ≤ k.val) : j ≠ k := by
    intro he
    subst j
    omega
  simp [SubexpCRTOuterInput.loaded, sweepStore, initializedStacks,
    SubexpCRTOuterInput.data, SubexpCRTOuterInput.store, hj,
    h104, h213, h214, h216, h225,
    hn 257 (by decide), hn 258 (by decide), hn 259 (by decide),
    hn 260 (by decide), hn 261 (by decide), hn 266 (by decide),
    hn 268 (by decide), hn 277 (by decide)]

omit [Fact p.Prime] in
theorem loaded_native (i : Fin 77) :
    L (nativePort i) = SubexpQuarticFlatMul.bankStore (fun _ => []) M.bits
      (SubexpQuarticFlatMul.flat t) width [] i := by
  rw [loaded_base p D M t one minusOne width exponent binaryD nodes jets
    processed remaining current acc (nativePort i) (by dsimp [nativePort]; omega)
    (by simp [nativePort, Fin.ext_iff]; omega)
    (by simp [nativePort, Fin.ext_iff]; omega)
    (by simp [nativePort, Fin.ext_iff]; omega)
    (by simp [nativePort, Fin.ext_iff]; omega)
    (by simp [nativePort, Fin.ext_iff]; omega)]
  simpa [nativePort, SubexpCRTOuterInput.baseContext,
    SubexpConvolutionPair.highPort, SubexpHornerMachine.flat_eq_encode] using
    SubexpCRTCanonicalInput.store_high
      (SubexpCRTOuterInput.baseContext p D M t one minusOne width exponent) i

omit [Fact p.Prime] in
theorem negation_view (i : Fin 24) :
    L (SubexpCRTOuterNeg.ports i) =
      SubexpCRTOuterNeg.blankStore minusOne.val M.bits width i := by
  fin_cases i <;>
    simp [SubexpCRTOuterNeg.ports, SubexpCRTOuterNeg.blankStore,
      SubexpQuarticFlatNeg.bankStore, SubexpQuarticFlatNeg.emptyBank,
      SubexpCRTOuterInput.loaded, sweepStore, initializedStacks,
      SubexpCRTOuterInput.data, SubexpCRTOuterInput.store,
      SubexpCRTOuterInput.baseContext, SubexpCRTCanonicalInput.store]

private theorem horner_range (i : Fin 87) :
    (128 ≤ (hornerPorts i).val ∧ (hornerPorts i).val < 205) ∨
      (246 ≤ (hornerPorts i).val ∧ (hornerPorts i).val < 256) := by
  change (128 ≤ (hornerPort i).val ∧ (hornerPort i).val < 205) ∨
    (246 ≤ (hornerPort i).val ∧ (hornerPort i).val < 256)
  by_cases hi : i.val < 77 <;> simp only [hornerPort, hi, ite_true, ite_false] <;> omega

omit [Fact p.Prime] in
theorem horner_view (x : SubexpCRTOuterInput.Coeff p D)
    (P : List (SubexpCRTOuterInput.Coeff p D)) (count : List Bool) (i : Fin 87) :
    L (hornerPorts i) =
      if i = 77 ∨ i = 78 ∨ i = 79 then [] else
        SubexpHornerControl.store
          (SubexpHornerMachine.initialWordsWithCount p (D + 1) M t x width P count) i := by
  refine Fin.addCases (m := 77) (n := 10) (fun j => ?_) (fun j => ?_) i
  · have hport : hornerPorts (Fin.castAdd 10 j) = nativePort j := by
      apply Fin.ext
      change (hornerPort (Fin.castAdd 10 j)).val = (nativePort j).val
      simp [hornerPort, nativePort]
    rw [hport, loaded_native p D M t one minusOne width exponent binaryD nodes jets
      processed remaining current acc j]
    fin_cases j <;>
      simp [SubexpQuarticFlatMul.bankStore, SubexpHornerControl.store,
        SubexpHornerMachine.initialWordsWithCount, SubexpHornerMachine.initialWords,
        SubexpHornerMachine.inputWords, SubexpHornerControl.readyWords,
        SubexpHornerMachine.baseWords]
  · have hport : hornerPorts (Fin.natAdd 77 j) =
        (⟨246 + j.val, by omega⟩ : Fin 320) := by
      apply Fin.ext
      change (hornerPort (Fin.natAdd 77 j)).val = 246 + j.val
      simp [hornerPort]
      omega
    rw [hport]
    rw [loaded_base p D M t one minusOne width exponent binaryD nodes jets
      processed remaining current acc (⟨246 + j.val, by omega⟩ : Fin 320)
      (by dsimp; omega)
      (by intro h; have hv := congrArg Fin.val h; norm_num at hv; omega)
      (by intro h; have hv := congrArg Fin.val h; norm_num at hv; omega)
      (by intro h; have hv := congrArg Fin.val h; norm_num at hv; omega)
      (by intro h; have hv := congrArg Fin.val h; norm_num at hv; omega)
      (by intro h; have hv := congrArg Fin.val h; norm_num at hv; omega)]
    fin_cases j <;>
      simp [SubexpCRTCanonicalInput.store, SubexpHornerControl.store,
        SubexpHornerMachine.initialWordsWithCount, SubexpHornerMachine.initialWords,
        SubexpHornerMachine.inputWords, SubexpHornerControl.readyWords,
        SubexpHornerMachine.baseWords]

/-- Empty weighted-service fields and the outer temporary/result ports. -/
def emptyPorts : List (Fin 320) :=
  [209, 210, 219, 220, 221, 222, 223, 224, 226, 227, 232, 235, 236,
    244, 262, 263, 264, 318, 319]

omit [Fact p.Prime] in
theorem loaded_empty (j : Fin 320) (hj : j ∈ emptyPorts) : L j = [] := by
  simp only [emptyPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [SubexpCRTOuterInput.loaded, sweepStore, initializedStacks,
      SubexpCRTOuterInput.data, SubexpCRTOuterInput.store,
      SubexpCRTOuterInput.baseContext, SubexpCRTCanonicalInput.store]

private theorem weighted_native (modulus reduction width : List Bool) :
    SubexpCRTCofactorControl.nativeStore
      (SubexpCRTOuterAccumulate.idleWords (weightedWords modulus reduction width)) =
      SubexpQuarticFlatMul.bankStore (fun _ => []) modulus reduction width [] := by
  funext i
  by_cases h70 : i = 70
  · subst i
    simp [SubexpCRTCofactorControl.nativeStore, SubexpCRTOuterAccumulate.idleWords,
      weightedWords, SubexpQuarticFlatMul.bankStore]
  · by_cases h71 : i = 71
    · subst i
      simp [SubexpCRTCofactorControl.nativeStore, SubexpCRTOuterAccumulate.idleWords,
        weightedWords, SubexpQuarticFlatMul.bankStore]
    · simp [SubexpCRTCofactorControl.nativeStore, SubexpCRTOuterAccumulate.idleWords,
        weightedWords, h70, h71]

omit [Fact p.Prime] in
theorem weighted_view (i : Fin 110) :
    L (scalarPorts i) =
      SubexpCRTCofactorControl.store (fun j => L (scalarPorts j))
        (SubexpCRTOuterAccumulate.idleWords
          (weightedWords M.bits (SubexpQuarticFlatMul.flat t) width)) i := by
  refine Fin.addCases (m := 77) (n := 33) (fun j => ?_) (fun j => ?_) i
  · simp only [SubexpCRTCofactorControl.store, Fin.val_castAdd, j.isLt, dite_true]
    exact (loaded_native p D M t one minusOne width exponent binaryD nodes jets
      processed remaining current acc j).trans
      (congrFun (weighted_native M.bits (SubexpQuarticFlatMul.flat t) width).symm j)
  · fin_cases j <;>
      simp [SubexpCRTCofactorControl.store, SubexpCRTOuterAccumulate.idleWords,
        weightedWords, Fin.coe_ofNat_eq_mod]
    all_goals
      apply loaded_empty p D M t one minusOne width exponent binaryD nodes jets
        processed remaining current acc
      decide

omit [Fact p.Prime] in
theorem loaded_dimension : L 243 = List.replicate D true := by
  rw [loaded_base p D M t one minusOne width exponent binaryD nodes jets
    processed remaining current acc 243 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  rfl

omit [Fact p.Prime] in
theorem loaded_current : L 259 = SubexpFlatAdd.encode (nodes current) := by
  simp [SubexpCRTOuterInput.loaded, sweepStore, loadedReady, loadedWords]

omit [Fact p.Prime] in
theorem loaded_accumulator : L 261 = SubexpFlatAdd.encode acc := by
  simp [SubexpCRTOuterInput.loaded, sweepStore, loadedReady, loadedWords, readyWords]

/-- Ports populated by the successive concrete services in one outer step. -/
def resultPorts : List (Fin 320) := [244, 262, 263, 264]

theorem negation_avoids (i : Fin 24) (j : Fin 320) (hj : j ∈ resultPorts) :
    SubexpCRTOuterNeg.ports i ≠ j := by
  simp only [resultPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;> fin_cases i <;> decide

theorem horner_avoids (i : Fin 87) (j : Fin 320) (hj : j ∈ resultPorts) :
    hornerPorts i ≠ j := by
  simp only [resultPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
  intro he
  have hrange := horner_range i
  have hv := congrArg Fin.val he
  rcases hj with rfl | rfl | rfl | rfl <;> norm_num at hv <;> omega

theorem scalar_avoids (i : Fin 110) (j : Fin 320) (hj : j ∈ resultPorts) :
    scalarPorts i ≠ j := by
  simp only [resultPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
  intro he
  have hv := congrArg Fin.val he
  change 128 + i.val = j.val at hv
  rcases hj with rfl | rfl | rfl | rfl <;> norm_num at hv <;> omega

@[simp] theorem update_negation (s : Fin 320 → List Bool) (j : Fin 320) (bits : List Bool)
    (hj : j ∈ resultPorts) (i : Fin 24) :
    Function.update s j bits (SubexpCRTOuterNeg.ports i) = s (SubexpCRTOuterNeg.ports i) :=
  Function.update_of_ne (negation_avoids i j hj) _ _

@[simp] theorem update_horner (s : Fin 320 → List Bool) (j : Fin 320) (bits : List Bool)
    (hj : j ∈ resultPorts) (i : Fin 87) :
    Function.update s j bits (hornerPorts i) = s (hornerPorts i) :=
  Function.update_of_ne (horner_avoids i j hj) _ _

@[simp] theorem update_scalar (s : Fin 320 → List Bool) (j : Fin 320) (bits : List Bool)
    (hj : j ∈ resultPorts) (i : Fin 110) :
    Function.update s j bits (scalarPorts i) = s (scalarPorts i) :=
  Function.update_of_ne (scalar_avoids i j hj) _ _

end SubexponentialSAT.SubexpCRTOuterScalarViews

end OAI.Algorithms
