import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseOps

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

/-- Used only as a finite counting envelope, never enumerated by the sparse operations. -/
def supportUniverse (vars : Finset V) (J : ℕ) : Finset (Finset V) :=
  vars.powerset.filter (fun s => s.card < J)

def indexUniverse (vars : Finset V) (t J : ℕ) : Finset (Index V) :=
  (((Finset.range t) ×ˢ (Finset.range J)) ×ˢ supportUniverse vars J).image
    (fun a => ⟨a.1.1, a.1.2, a.2⟩)

theorem mem_indexUniverse (vars : Finset V) (t J : ℕ) (a : Index V) :
    a ∈ indexUniverse vars t J ↔ a.Kept t J ∧ a.vars ⊆ vars ∧ a.vars.card < J := by
  rcases a with ⟨u, z, s⟩
  simp [indexUniverse, supportUniverse, Index.Kept, Finset.mem_image]

theorem indexUniverse_card_le (vars : Finset V) (t J : ℕ) :
    (indexUniverse vars t J).card ≤ t * J * (supportUniverse vars J).card := by
  exact (Finset.card_image_le).trans (by simp)

def ValidData (vars : Finset V) (t J : ℕ) (l : Data (Index V) R) : Prop :=
  ∀ a ∈ keys l, a.Kept t J ∧ a.Valid ∧ a.vars ⊆ vars

theorem ValidData.normalize {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) : ValidData vars t J (normalize l) := by
  intro a ha
  exact h a ((mem_keys_normalize a l).mp ha)

omit [CommSemiring R] in
theorem ValidData.in_universe {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) : ∀ a ∈ keys l, a ∈ indexUniverse vars t J := by
  intro a ha
  rcases h a ha with ⟨hk, hv, hs⟩
  exact (mem_indexUniverse vars t J a).mpr ⟨hk, hs, hv.trans_lt hk.2⟩

omit [CommSemiring R] in
theorem ValidData.length_le {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) (hn : (keys l).Nodup) :
    l.length ≤ t * J * (supportUniverse vars J).card :=
  (length_le_card l _ hn h.in_universe).trans (indexUniverse_card_le vars t J)

theorem ValidData.add {vars : Finset V} {t J : ℕ} {a b : Data (Index V) R}
    (ha : ValidData vars t J a) (hb : ValidData vars t J b) : ValidData vars t J (add a b) := by
  apply ValidData.normalize
  intro k hk
  have : k ∈ keys a ∨ k ∈ keys b := by simpa [keys] using hk
  exact this.elim (ha k) (hb k)

omit [DecidableEq V] in
theorem ValidData.scale {vars : Finset V} {t J : ℕ} {a : Data (Index V) R}
    (ha : ValidData vars t J a) (c : R) : ValidData vars t J (scale c a) := by
  intro k hk
  rw [keys_scale] at hk
  exact ha k hk

theorem ValidData.admissible {vars : Finset V} {t J : ℕ} {a : Data (Index V) R}
    (ha : ValidData vars t J a) : Admissible (denote a) := by
  induction a with
  | nil => exact admissible_zero
  | cons q a ih =>
      have hq : q.1 ∈ keys (q :: a) := by simp [keys]
      have htail : ValidData vars t J a := by
        intro k hk; exact ha k (by simp [keys] at hk ⊢; exact Or.inr hk)
      exact (atom_admissible q.1 q.2 (ha q.1 hq).2.1).add (ih htail)

theorem ValidData.canonical {vars : Finset V} {t J : ℕ} {a : Data (Index V) R}
    (ha : ValidData vars t J a) : canonical t J (denote a) = denote a := by
  induction a with
  | nil => simp [denote, decode]
  | cons q a ih =>
      have hq : q.1 ∈ keys (q :: a) := by simp [keys]
      have htail : ValidData vars t J a := by
        intro k hk; exact ha k (by simp [keys] at hk ⊢; exact Or.inr hk)
      change Squarefree.canonical t J (atom q.1 q.2 + denote a) = atom q.1 q.2 + denote a
      rw [map_add, canonical_atom, ite_eq_left (ha q.1 hq).1, ih htail]

omit [DecidableEq V] [CommSemiring R] in
theorem constant_valid (vars : Finset V) (t J : ℕ) (c : R) :
    ValidData vars t J (constant t J c) := by
  by_cases h : 0 < t ∧ 0 < J
  · simp [constant, h, ValidData, keys, Index.Kept, Index.Valid, Index.origin ]
  · simp [constant, h, ValidData, keys]

theorem mem_keys_row (t J : ℕ) (a : Index V × R) (b : Data (Index V) R) (k : Index V) :
    k ∈ keys (row t J a b) ↔ ∃ q ∈ b, k = a.1.join q.1 ∧ k.Kept t J := by
  induction b with
  | nil => simp [row, keys]
  | cons q b ih =>
      by_cases h : (a.1.join q.1).Kept t J
      · simp only [row, ite_eq_left h]
        change k ∈ (a.1.join q.1 :: keys (row t J a b)) ↔ _
        rw [List.mem_cons, ih]
        simp only [List.mem_cons, exists_eq_or_imp]
        aesop
      · simp only [row, ite_eq_right h, ih]
        simp only [List.mem_cons, exists_eq_or_imp]
        aesop

theorem ValidData.row {vars : Finset V} {t J : ℕ} {a : Index V × R}
    {b : Data (Index V) R} (ha : a.1.Valid ∧ a.1.vars ⊆ vars)
    (hb : ValidData vars t J b) : ValidData vars t J (row t J a b) := by
  intro k hk
  obtain ⟨q, hq, rfl, hkeep⟩ := (mem_keys_row t J a b k).mp hk
  have hqk : q.1 ∈ keys b := List.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨_, hv, hs⟩ := hb q.1 hqk
  exact ⟨hkeep, ha.1.join hv, Finset.union_subset ha.2 hs⟩

theorem ValidData.rawMul {vars : Finset V} {t J : ℕ} {a b : Data (Index V) R}
    (ha : ValidData vars t J a) (hb : ValidData vars t J b) :
    ValidData vars t J (rawMul t J a b) := by
  induction a with
  | nil => simp [Sparse.rawMul, ValidData, keys]
  | cons q a ih =>
      have hq : q.1 ∈ keys (q :: a) := by simp [keys]
      have htail : ValidData vars t J a := by
        intro k hk; exact ha k (by simp [keys] at hk ⊢; exact Or.inr hk)
      have hrow := ValidData.row (a := q) (ha q.1 hq).2 hb
      intro k hk
      have hor : k ∈ keys (Sparse.row t J q b) ∨ k ∈ keys (Sparse.rawMul t J a b) := by
        simpa [Sparse.rawMul, keys] using hk
      exact hor.elim (hrow k) (ih htail k)

theorem ValidData.mul {vars : Finset V} {t J : ℕ} {a b : Data (Index V) R}
    (ha : ValidData vars t J a) (hb : ValidData vars t J b) :
    ValidData vars t J (mul t J a b) := (ha.rawMul hb).normalize

/-- Arithmetic and dictionary-scan units. Key and coefficient bit costs are external multipliers. -/
def mulWork (t J : ℕ) (a b : Data (Index V) R) : ℕ :=
  a.length * b.length + normalizeWork (rawMul t J a b)

theorem mulWork_le {vars : Finset V} {t J : ℕ} {a b : Data (Index V) R}
    (ha : ValidData vars t J a) (hb : ValidData vars t J b) :
    mulWork t J a b ≤ a.length * b.length *
      (2 * (indexUniverse vars t J).card + 2) := by
  have hnorm := normalizeWork_le (rawMul t J a b) (indexUniverse vars t J)
    (ha.rawMul hb).in_universe
  have hlen := rawMul_length_le t J a b
  calc
    mulWork t J a b ≤ a.length * b.length +
        (rawMul t J a b).length * (2 * (indexUniverse vars t J).card + 1) :=
      Nat.add_le_add_left hnorm _
    _ ≤ a.length * b.length + a.length * b.length *
        (2 * (indexUniverse vars t J).card + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) _
    _ = a.length * b.length * (2 * (indexUniverse vars t J).card + 2) := by ring

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
