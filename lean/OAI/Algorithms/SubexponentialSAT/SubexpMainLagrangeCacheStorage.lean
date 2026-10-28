import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLagrangeCachePorts
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Physical clearing around the native target Lagrange cache

Every non-input word, including the old output, is erased before the native
call.  The final pass clears all scratch words and resets all sixteen local
registers.  Neither pass writes an input or the new output.
-/

namespace SubexponentialSAT.SubexpMainLagrangeCache

open BitProgram StructuredCalls SubexpSetupStorage
open SubexpLagrangeCachePreparation (Inputs rawStore rawState)

abbrev LocalState := State 16 256

def localInputs (a : LocalState) : Inputs where
  prime := a.stacks 206
  unit := a.stacks 207
  modulus := a.stacks 208
  width := a.stacks 209
  reduction := a.stacks 210
  minusOne := a.stacks 211
  precision := a.stacks 224
  exponent := a.stacks 225

theorem localInputs_word (a : LocalState) (i : Fin 8) :
    SubexpLagrangeCachePreparation.inputWords (localInputs a) i = a.stacks (inputPort i) := by
  fin_cases i <;> rfl

def preparePorts : List (Fin 256) :=
  (List.finRange 256).filter (fun i => decide (inputIndex i = none))

def cleanupPorts : List (Fin 256) := preparePorts.filter (fun i => decide (i ≠ 250))

@[simp] theorem mem_preparePorts (i : Fin 256) :
    i ∈ preparePorts ↔ inputIndex i = none := by
  simp [preparePorts]

@[simp] theorem mem_cleanupPorts (i : Fin 256) :
    i ∈ cleanupPorts ↔ inputIndex i = none ∧ i ≠ 250 := by
  simp [cleanupPorts]

private theorem filter_length_split {S : Type} (f : S → Bool) (n : ℕ) (xs : List S) :
    (xs.filter f).length = ((xs.take n).filter f).length + ((xs.drop n).filter f).length := by
  rw [← List.length_append, ← List.filter_append, List.take_append_drop]

theorem preparePorts_length : preparePorts.length = 248 := by
  let xs := List.finRange 256
  let f := fun i : Fin 256 ↦ decide (inputIndex i = none)
  change (xs.filter f).length = 248
  rw [filter_length_split f 32 xs,
    filter_length_split f 32 (xs.drop 32),
    filter_length_split f 32 ((xs.drop 32).drop 32),
    filter_length_split f 32 (((xs.drop 32).drop 32).drop 32),
    filter_length_split f 32 ((((xs.drop 32).drop 32).drop 32).drop 32),
    filter_length_split f 32 (((((xs.drop 32).drop 32).drop 32).drop 32).drop 32),
    filter_length_split f 32 ((((((xs.drop 32).drop 32).drop 32).drop 32).drop 32).drop 32)]
  have h₀ : (((xs.take 32).filter f).length) = 32 := by decide
  have h₁ : ((((xs.drop 32).take 32).filter f).length) = 32 := by decide
  have h₂ : (((((xs.drop 32).drop 32).take 32).filter f).length) = 32 := by decide
  have h₃ : ((((((xs.drop 32).drop 32).drop 32).take 32).filter f).length) = 32 := by
    decide
  have h₄ : (((((((xs.drop 32).drop 32).drop 32).drop 32).take 32).filter f).length) =
      32 := by
    decide
  have h₅ : ((((((((xs.drop 32).drop 32).drop 32).drop 32).drop 32).take 32).filter f).length) =
      32 := by
    decide
  have h₆ : (((((((((xs.drop 32).drop 32).drop 32).drop 32).drop 32).drop 32).take 32).filter f).length) =
      26 := by
    decide
  have h₇ : (((((((((xs.drop 32).drop 32).drop 32).drop 32).drop 32).drop 32).drop 32).filter f).length) =
      30 := by
    decide
  omega

theorem cleanupPorts_length : cleanupPorts.length = 247 := by
  have hnodup : preparePorts.Nodup := (List.nodup_finRange 256).filter _
  have hmem : (250 : Fin 256) ∈ preparePorts := by
    simp [inputIndex]
  have hlength := List.length_erase_add_one hmem
  have hpred : (fun i : Fin 256 ↦ decide (i ≠ 250)) = fun i ↦ i != 250 := by
    funext i
    apply Bool.eq_iff_iff.mpr
    simp
  rw [cleanupPorts, hpred, ← hnodup.erase_eq_filter]
  rw [preparePorts_length] at hlength
  omega

abbrev prepare : Cmd 16 256 := clearMany preparePorts
def prepared (a : LocalState) : LocalState := clearManyState preparePorts a
def prepareCost (a : LocalState) : ℕ := clearManyCost preparePorts a

theorem prepare_eval (a : LocalState) : Eval prepare (prepareCost a) a (prepared a) :=
  clearMany_eval preparePorts a

theorem prepared_stacks (a : LocalState) : (prepared a).stacks = rawStore (localInputs a) := by
  funext i
  rw [prepared, clearMany_stacks]
  cases hi : inputIndex i with
  | none =>
    rw [ite_eq_left ((mem_preparePorts i).mpr hi), rawStore_other _ _ hi]
  | some j =>
    have he := inputIndex_eq_some hi
    have hn : i ∉ preparePorts := by simp [hi]
    rw [ite_eq_right hn, he, rawStore_input, localInputs_word]

theorem prepared_rawState (a : LocalState) :
    prepared a = rawState (localInputs a) (prepared a).regs := by
  exact SubexpScanPrimitives.state_ext (a := prepared a)
    (b := rawState (localInputs a) (prepared a).regs) rfl (prepared_stacks a)

abbrev finish : Cmd 16 256 := .seq (clearMany cleanupPorts) RegisterResetProgram.all
def finished (a : LocalState) : LocalState :=
  RegisterResetProgram.zeroed (clearManyState cleanupPorts a)

private theorem clearManyCost_empty {S : ℕ} (ports : List (Fin S)) (a : Data S)
    (h : ∀ i ∈ ports, a.stacks i = []) : clearManyCost ports a = 3 * ports.length := by
  induction ports generalizing a with
  | nil => rfl
  | cons p ps ih =>
    have hp : a.stacks p = [] := h p List.mem_cons_self
    have hs : ∀ i ∈ ps, (clearState p a).stacks i = [] := by
      intro i hi
      by_cases he : i = p
      · subst i; simp [clearState]
      · simp only [clearState, Function.update_of_ne he]
        exact h i (List.mem_cons_of_mem _ hi)
    simp only [clearManyCost, hp, List.length_nil, Nat.mul_zero, Nat.zero_add,
      ih _ hs, List.length_cons]
    omega

private theorem clearManyCost_le_on {S : ℕ} (ports : List (Fin S)) (a : Data S) (B : ℕ)
    (h : ∀ i ∈ ports, (a.stacks i).length ≤ B) :
    clearManyCost ports a ≤ ports.length * (2 * B + 3) := by
  induction ports generalizing a with
  | nil => simp [clearManyCost]
  | cons p ps ih =>
    have hp : (a.stacks p).length ≤ B := h p List.mem_cons_self
    have hs : ∀ i ∈ ps, ((clearState p a).stacks i).length ≤ B := by
      intro i hi
      by_cases he : i = p
      · subst i; simp [clearState]
      · simp only [clearState, Function.update_of_ne he]
        exact h i (List.mem_cons_of_mem _ hi)
    have hc := ih (clearState p a) hs
    calc
      clearManyCost (p :: ps) a =
          2 * (a.stacks p).length + 3 + clearManyCost ps (clearState p a) := rfl
      _ ≤ (2 * B + 3) + ps.length * (2 * B + 3) := by omega
      _ = (p :: ps).length * (2 * B + 3) := by simp only [List.length_cons]; ring

theorem prepareCost_le (a : LocalState) (B : ℕ)
    (h : ∀ i, inputIndex i = none → (a.stacks i).length ≤ B) :
    prepareCost a ≤ 248 * (2 * B + 3) := by
  have ht := clearManyCost_le_on preparePorts a B (fun i hi => h i ((mem_preparePorts i).mp hi))
  simpa only [prepareCost, preparePorts_length] using ht

theorem cleanup_empty (a : LocalState) (x : Inputs) (bytes : List Bool)
    (h : a.stacks = Function.update (rawStore x) 250 bytes) :
    ∀ i ∈ cleanupPorts, a.stacks i = [] := by
  intro i hi
  obtain ⟨hn, ho⟩ := (mem_cleanupPorts i).mp hi
  rw [h, Function.update_of_ne ho, rawStore_other x i hn]

theorem finished_stacks (a : LocalState) (x : Inputs) (bytes : List Bool)
    (h : a.stacks = Function.update (rawStore x) 250 bytes) :
    (finished a).stacks = Function.update (rawStore x) 250 bytes := by
  change (clearManyState cleanupPorts a).stacks = _
  funext i
  rw [clearMany_stacks]
  by_cases hi : i ∈ cleanupPorts
  · rw [ite_eq_left hi]
    exact (cleanup_empty a x bytes h i hi).symm.trans (congrFun h i)
  · rw [ite_eq_right hi]
    exact congrFun h i

theorem finish_eval (a : LocalState) (x : Inputs) (bytes : List Bool)
    (h : a.stacks = Function.update (rawStore x) 250 bytes) :
    Eval finish 757 a (finished a) := by
  have hc := clearMany_eval cleanupPorts a
  rw [clearManyCost_empty cleanupPorts a (cleanup_empty a x bytes h), cleanupPorts_length] at hc
  exact hc.seq (RegisterResetProgram.all_eval (clearManyState cleanupPorts a))

theorem finished_regs (a : LocalState) : (finished a).regs = fun _ => false := rfl

end SubexponentialSAT.SubexpMainLagrangeCache

end OAI.Algorithms
