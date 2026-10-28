import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeJet

namespace OAI.Algorithms

/-! Computable normalized sparse coefficient lists. Zero coefficients may stay
in the list; keys are unique, so this does not enlarge the finite index bound.
No equality decision for coefficients or full ambient Boolean table is used. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {K R A : Type*} [DecidableEq K] [AddCommMonoid R]

abbrev Data (K R : Type*) := List (K × R)

def keys (l : Data K R) : List K := l.map Prod.fst

def fetch (k : K) : Data K R → R
  | [] => 0
  | (j, c) :: l => (if j = k then c else 0) + fetch k l

def erase (k : K) (l : Data K R) : Data K R := l.filter (fun a => decide (a.1 ≠ k))

def insert (k : K) (c : R) (l : Data K R) : Data K R :=
  (k, c + fetch k l) :: erase k l

def normalize : Data K R → Data K R
  | [] => []
  | a :: l => insert a.1 a.2 (normalize l)

def add (a b : Data K R) : Data K R := normalize (a ++ b)

omit [AddCommMonoid R] in
theorem keys_erase (k : K) (l : Data K R) :
    keys (erase k l) = (keys l).filter (fun j => decide (j ≠ k)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : a.1 = k <;> simp [erase, keys, h] at ih ⊢ <;> exact ih

@[simp] theorem mem_keys_insert (k j : K) (c : R) (l : Data K R) :
    j ∈ keys (insert k c l) ↔ j = k ∨ j ∈ keys l := by
  simp only [insert, keys, List.map_cons, List.mem_cons]
  change j = k ∨ j ∈ keys (erase k l) ↔ j = k ∨ j ∈ keys l
  rw [keys_erase]
  simp only [List.mem_filter, decide_eq_true_eq]
  tauto

theorem nodup_insert (k : K) (c : R) (l : Data K R) (h : (keys l).Nodup) :
    (keys (insert k c l)).Nodup := by
  change (k :: keys (erase k l)).Nodup
  rw [keys_erase, List.nodup_cons]
  exact ⟨by simp, h.filter _⟩

theorem nodup_normalize (l : Data K R) : (keys (normalize l)).Nodup := by
  induction l with
  | nil => simp [normalize, keys]
  | cons a l ih => exact nodup_insert _ _ _ ih

@[simp] theorem mem_keys_normalize (k : K) (l : Data K R) :
    k ∈ keys (normalize l) ↔ k ∈ keys l := by
  induction l with
  | nil => simp [normalize, keys]
  | cons a l ih =>
      rw [normalize, mem_keys_insert, ih]
      simp only [keys, List.map_cons, List.mem_cons]

omit [AddCommMonoid R] in
theorem length_le_card (l : Data K R) (s : Finset K) (hn : (keys l).Nodup)
    (hs : ∀ k ∈ keys l, k ∈ s) : l.length ≤ s.card := by
  have hsub : (keys l).toFinset ⊆ s := by
    intro k hk
    exact hs k (List.mem_toFinset.mp hk)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn] at hcard
  simpa only [keys, List.length_map] using hcard

theorem normalize_length_le (l : Data K R) (s : Finset K)
    (hs : ∀ k ∈ keys l, k ∈ s) : (normalize l).length ≤ s.card := by
  apply length_le_card _ s (nodup_normalize l)
  simpa using hs

/-- Number of elementary scans/additions in the explicitly written normalization.
Each insertion scans the current dictionary twice and writes one head entry. -/
def normalizeWork : Data K R → ℕ
  | [] => 0
  | _ :: l => normalizeWork l + 2 * (normalize l).length + 1

theorem normalizeWork_le (l : Data K R) (s : Finset K)
    (hs : ∀ k ∈ keys l, k ∈ s) : normalizeWork l ≤ l.length * (2 * s.card + 1) := by
  induction l with
  | nil => simp [normalizeWork]
  | cons a l ih =>
      have ht : ∀ k ∈ keys l, k ∈ s := by
        intro k hk; exact hs k (by simp [keys] at hk ⊢; exact Or.inr hk)
      have hl := normalize_length_le l s ht
      have hi := ih ht
      simp only [normalizeWork, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

section Decode

variable [AddCommMonoid A]

def decode (atom : K → R → A) : Data K R → A
  | [] => 0
  | (k, c) :: l => atom k c + decode atom l

omit [DecidableEq K] [AddCommMonoid R] in
theorem decode_append (atom : K → R → A) (a b : Data K R) :
    decode atom (a ++ b) = decode atom a + decode atom b := by
  induction a with
  | nil => simp [decode]
  | cons h a ih => simp [decode, ih, add_assoc]

theorem decode_split (atom : K → R → A) (hzero : ∀ k, atom k 0 = 0)
    (hadd : ∀ k a b, atom k (a + b) = atom k a + atom k b) (k : K) (l : Data K R) :
    decode atom l = atom k (fetch k l) + decode atom (erase k l) := by
  induction l with
  | nil => simp [decode, fetch, erase, hzero]
  | cons a l ih =>
      rcases a with ⟨j, c⟩
      by_cases h : j = k
      · subst j
        simpa [decode, fetch, erase, hadd, add_assoc] using congrArg (atom k c + ·) ih
      · simp [decode, fetch, erase, h, ih, add_left_comm]

theorem decode_insert (atom : K → R → A) (hzero : ∀ k, atom k 0 = 0)
    (hadd : ∀ k a b, atom k (a + b) = atom k a + atom k b)
    (k : K) (c : R) (l : Data K R) :
    decode atom (insert k c l) = atom k c + decode atom l := by
  simp only [insert, decode, hadd, add_assoc]
  rw [← decode_split atom hzero hadd]

theorem decode_normalize (atom : K → R → A) (hzero : ∀ k, atom k 0 = 0)
    (hadd : ∀ k a b, atom k (a + b) = atom k a + atom k b) (l : Data K R) :
    decode atom (normalize l) = decode atom l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [normalize, decode, decode_insert atom hzero hadd, ih]

theorem decode_add (atom : K → R → A) (hzero : ∀ k, atom k 0 = 0)
    (hadd : ∀ k a b, atom k (a + b) = atom k a + atom k b) (a b : Data K R) :
    decode atom (add a b) = decode atom a + decode atom b := by
  rw [add, decode_normalize atom hzero hadd, decode_append]

end Decode
end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
