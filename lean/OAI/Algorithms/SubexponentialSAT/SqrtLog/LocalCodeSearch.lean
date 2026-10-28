import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCodeLogBound

namespace OAI.Algorithms

/-! Executable exhaustive enumeration and its complete-search specification. -/

namespace SubexponentialSAT.SqrtLog.LocalCode

open SparseCode

def enumerateFunctions {α : Type*} (values : List α) : (d : ℕ) → List (Fin d → α)
  | 0 => [Fin.elim0]
  | d + 1 => values.flatMap fun a =>
      (enumerateFunctions values d).map (Fin.cons a)

theorem enumerateFunctions_complete {α : Type*} (values : List α)
    (hvalues : ∀ a, a ∈ values) (d : ℕ) (f : Fin d → α) :
    f ∈ enumerateFunctions values d := by
  induction d with
  | zero =>
      have hf : f = Fin.elim0 := by ext i; exact Fin.elim0 i
      simp [enumerateFunctions, hf]
  | succ d ih =>
      apply List.mem_flatMap.mpr
      refine ⟨f 0, hvalues _, List.mem_map.mpr ?_⟩
      exact ⟨Fin.tail f, ih _, Fin.cons_self_tail f⟩

theorem enumerateFunctions_length {α : Type*} (values : List α) (d : ℕ) :
    (enumerateFunctions values d).length = values.length ^ d := by
  induction d with
  | zero => simp [enumerateFunctions]
  | succ d ih =>
      simp [enumerateFunctions, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

def localAlphabet : List F3 := [0, 1, 2]

theorem localAlphabet_complete : ∀ a : F3, a ∈ localAlphabet := by decide

@[simp] theorem localAlphabet_length : localAlphabet.length = 3 := rfl

theorem localAlphabet_encoding : localAlphabet.map ZMod.val = [0, 1, 2] := by decide

def localWords (D : ℕ) : List (Fin D → F3) :=
  enumerateFunctions localAlphabet D

theorem localWords_complete (D : ℕ) (w : Fin D → F3) : w ∈ localWords D := by
  apply enumerateFunctions_complete
  exact localAlphabet_complete

@[simp] theorem localWords_length (D : ℕ) : (localWords D).length = 3 ^ D := by
  simp [localWords, enumerateFunctions_length]

def localMatrices (D t : ℕ) : List (CheckMatrix (Fin t) (Fin D)) :=
  enumerateFunctions (localWords D) t

theorem localMatrices_complete (D t : ℕ) (Q : CheckMatrix (Fin t) (Fin D)) :
    Q ∈ localMatrices D t :=
  enumerateFunctions_complete _ (localWords_complete D) t Q

@[simp] theorem localMatrices_length (D t : ℕ) :
    (localMatrices D t).length = 3 ^ (t * D) := by
  change (enumerateFunctions (localWords D) t).length = _
  rw [enumerateFunctions_length, localWords_length, ← pow_mul, Nat.mul_comm D t]

instance decidableIsCodeword {D t : ℕ} (Q : CheckMatrix (Fin t) (Fin D))
    (w : Fin D → F3) : Decidable (IsCodeword Q w) := by
  unfold IsCodeword
  infer_instance

instance decidableHasDistance {D t : ℕ} (Q : CheckMatrix (Fin t) (Fin D))
    (d : ℕ) : Decidable (HasDistance Q d) := by
  unfold HasDistance
  infer_instance

/-- The test explicitly scans the complete list of ternary words. -/
def localCodeTest (D t d : ℕ) (Q : CheckMatrix (Fin t) (Fin D)) : Bool :=
  (localWords D).all fun w => decide (IsCodeword Q w → w ≠ 0 → d ≤ weight w)

theorem localCodeTest_spec (D t d : ℕ) (Q : CheckMatrix (Fin t) (Fin D)) :
    localCodeTest D t d Q = true ↔ HasDistance Q d := by
  simp only [localCodeTest, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h w hw hw0
    exact h w (localWords_complete D w) hw hw0
  · intro h w _
    exact h w

def localCodeSearch (D t d : ℕ) : Option (CheckMatrix (Fin t) (Fin D)) :=
  (localMatrices D t).find? (localCodeTest D t d)

theorem localCodeSearch_sound {D t d : ℕ} {Q : CheckMatrix (Fin t) (Fin D)}
    (h : localCodeSearch D t d = some Q) : HasDistance Q d := by
  have hp := List.find?_some h
  exact (localCodeTest_spec D t d Q).mp hp

theorem localCodeSearch_complete {D t d : ℕ}
    (hex : ∃ Q : CheckMatrix (Fin t) (Fin D), HasDistance Q d) :
    ∃ Q, localCodeSearch D t d = some Q := by
  cases hs : localCodeSearch D t d with
  | none =>
      obtain ⟨Q, hQ⟩ := hex
      have hall := List.find?_eq_none.mp hs
      have hf := hall Q (localMatrices_complete D t Q)
      exact (hf ((localCodeTest_spec D t d Q).mpr hQ)).elim
  | some Q => exact ⟨Q, rfl⟩

/-- An executable total constructor. Under the proved numerical hypotheses,
the fallback is never used. -/
def localMatrix (D B ell t : ℕ) : CheckMatrix (Fin t) (Fin D) :=
  (localCodeSearch D t (D / (100 * B * ell) + 1)).getD 0

theorem localMatrix_distance (D B ell t : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hD : D ≤ 2 ^ ell)
    (ht : D ≤ 8 * B * t) :
    HasDistance (localMatrix D B ell t) (D / (100 * B * ell) + 1) := by
  obtain ⟨Q, hQ⟩ := localCodeSearch_complete
    (exists_local_code_log_bound D B ell t hB hell hD ht)
  simpa [localMatrix, hQ] using localCodeSearch_sound hQ

theorem localMatrix_relativeDistance (D B ell t : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hD : D ≤ 2 ^ ell)
    (ht : D ≤ 8 * B * t) :
    HasRelativeDistance (localMatrix D B ell t)
      (1 / (100 * (B : ℝ) * (ell : ℝ))) :=
  relative_of_log_distance hB hell _ (localMatrix_distance D B ell t hB hell hD ht)

end SubexponentialSAT.SqrtLog.LocalCode

end OAI.Algorithms
