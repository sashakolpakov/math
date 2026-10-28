import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectCore

namespace OAI.Algorithms

/-! An executable finite argmin. Scores are natural numbers, not unary
word lengths. The companion trace records both score calls at every scan
step, including repeated calls and all losing candidates. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

variable {R : Type*}

def best (score : R → ℕ) (seed : R) : List R → R
  | [] => seed
  | r :: rs => best score (if score r < score seed then r else seed) rs

def bestTrace (score : R → ℕ) (seed : R) : List R → List R
  | [] => []
  | r :: rs => r :: seed ::
      bestTrace score (if score r < score seed then r else seed) rs

theorem best_le_seed (score : R → ℕ) (seed : R) (rs : List R) :
    score (best score seed rs) ≤ score seed := by
  induction rs generalizing seed with
  | nil => simp [best]
  | cons r rs ih =>
    simp only [best]
    split_ifs with h
    · exact (ih r).trans (Nat.le_of_lt h)
    · exact ih seed

theorem best_le_member (score : R → ℕ) (seed : R) (rs : List R)
    (r : R) (hr : r ∈ rs) :
    score (best score seed rs) ≤ score r := by
  induction rs generalizing seed with
  | nil => simp at hr
  | cons a rs ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst a
      simp only [best]
      split_ifs with hs
      · exact best_le_seed score r rs
      · exact (best_le_seed score seed rs).trans (Nat.le_of_not_gt hs)
    · simp only [best]
      exact ih _ h

theorem best_mem (score : R → ℕ) (seed : R) (rs : List R) :
    best score seed rs ∈ seed :: rs := by
  induction rs generalizing seed with
  | nil => simp [best]
  | cons r rs ih =>
    simp only [best]
    by_cases hs : score r < score seed
    · simp only [hs, ↓reduceIte]
      exact List.mem_cons_of_mem seed (ih r)
    · simp only [hs, ↓reduceIte]
      rcases List.mem_cons.mp (ih seed) with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem bestTrace_length (score : R → ℕ) (seed : R) (rs : List R) :
    (bestTrace score seed rs).length = 2 * rs.length := by
  induction rs generalizing seed with
  | nil => simp [bestTrace]
  | cons r rs ih => simp [bestTrace, ih, Nat.mul_add, Nat.add_assoc]

theorem bestTrace_mem (score : R → ℕ) (seed : R) (rs : List R)
    (r : R) (hr : r ∈ bestTrace score seed rs) : r ∈ seed :: rs := by
  induction rs generalizing seed with
  | nil => simp [bestTrace] at hr
  | cons a rs ih =>
    simp only [bestTrace, List.mem_cons] at hr
    rcases hr with h | h | h
    · simp [h]
    · simp [h]
    · have h' := ih _ h
      rcases List.mem_cons.mp h' with h' | h'
      · split_ifs at h' <;> simp [h']
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')

def pick {c : ℕ} (score : R → ℕ) (family : Fin (c + 1) → R) : R :=
  best score (family 0) (List.ofFn family)

theorem pick_le {c : ℕ} (score : R → ℕ) (family : Fin (c + 1) → R)
    (i : Fin (c + 1)) : score (pick score family) ≤ score (family i) := by
  apply best_le_member
  simp only [List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem pick_mem {c : ℕ} (score : R → ℕ) (family : Fin (c + 1) → R) :
    ∃ i, pick score family = family i := by
  have h := best_mem score (family 0) (List.ofFn family)
  rcases List.mem_cons.mp h with h | h
  · exact ⟨0, h⟩
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact ⟨i, hi.symm⟩

theorem pick_property {c : ℕ} (score : R → ℕ)
    (family : Fin (c + 1) → R) (P : R → Prop)
    (hP : ∀ i, P (family i)) : P (pick score family) := by
  rcases pick_mem score family with ⟨i, hi⟩
  rw [hi]
  exact hP i

def pickTrace {c : ℕ} (score : R → ℕ) (family : Fin (c + 1) → R) : List R :=
  bestTrace score (family 0) (List.ofFn family)

theorem pickTrace_length {c : ℕ} (score : R → ℕ)
    (family : Fin (c + 1) → R) :
    (pickTrace score family).length = 2 * (c + 1) := by
  simp [pickTrace, bestTrace_length]

theorem pickTrace_property {c : ℕ} (score : R → ℕ)
    (family : Fin (c + 1) → R) (P : R → Prop)
    (hP : ∀ i, P (family i)) :
    ∀ r ∈ pickTrace score family, P r := by
  intro r hr
  have h := bestTrace_mem score (family 0) (List.ofFn family) r hr
  rcases List.mem_cons.mp h with h | h
  · simpa [h] using hP 0
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    simpa [hi] using hP i

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
