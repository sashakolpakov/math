import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramStored
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramValidity
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProductBounds

namespace OAI.Algorithms

/-! Finite record capacity for the actual normalized stored lists. The finite
universe is used for counting only; the program never enumerates it. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram

def capacity {n : ℕ} (vars : Finset (Fin n)) (u J : ℕ) : ℕ :=
  u * J * (Squarefree.Sparse.supportUniverse vars J).card

def Valid {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) : Prop :=
  ∀ a ∈ entries, Product.ValidKey vars u J a.1

def Good {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) : Prop :=
  Valid vars u J entries ∧ (Squarefree.Sparse.keys entries).Nodup

theorem valid_nil {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ) :
    Valid vars u J ([] : List (Product.Entry n B d)) := by
  intro a ha
  simp at ha

theorem good_nil {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ) :
    Good vars u J ([] : List (Product.Entry n B d)) :=
  ⟨valid_nil vars u J, by simp [Squarefree.Sparse.keys]⟩

theorem length_le_capacity {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) (h : Good vars u J entries) :
    entries.length ≤ capacity vars u J := by
  have hs : (Squarefree.Sparse.keys entries).toFinset ⊆
      Squarefree.Sparse.indexUniverse vars u J := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    have hh := h.1 a ha
    exact (Squarefree.Sparse.mem_indexUniverse vars u J a.1).mpr
      ⟨hh.1, hh.2.2, hh.2.1.trans_lt hh.1.2⟩
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup h.2] at hc
  have hl : entries.length ≤ (Squarefree.Sparse.indexUniverse vars u J).card := by
    simpa only [Squarefree.Sparse.keys,List.length_map] using hc
  exact hl.trans (Squarefree.Sparse.indexUniverse_card_le vars u J)

theorem valid_keyBound {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) (h : Valid vars u J entries) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) entries := by
  intro a ha
  have hh := Squarefree.encodeIndex_length_le a.1 (h a ha).1
  omega

def byteCapacity (n B d u J N : ℕ) : ℕ := N * (2*(n+u+J)+2*(d*B)+2)

theorem bytes_le_capacity {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) (h : Good vars u J entries) :
    (Product.bytes entries).length ≤ byteCapacity n B d u J (capacity vars u J) := by
  exact (Product.bytes_length_le entries (n+u+J) (valid_keyBound vars u J entries h.1)).trans
    (Nat.mul_le_mul_right _ (length_le_capacity vars u J entries h))

variable {p t n d : ℕ} [Fact p.Prime]

omit [Fact (Nat.Prime p)] in
theorem constant_good (cache : RingProgram.ScalarCache p t)
    (vars : Finset (Fin n)) (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (word : RingProgram.ScalarCode p t) :
    Good vars u J (constantStored p t cache (d:=d) word) := by
  refine ⟨?_, constantStored_nodup p t cache word⟩
  intro a ha
  simp only [constantStored,List.mem_singleton] at ha
  subst a
  simp [Product.ValidKey,Squarefree.Index.origin,Squarefree.Index.Kept,
    Squarefree.Index.Valid,hu,hJ]

theorem add_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) (vars : Finset (Fin n)) (u J : ℕ)
    (a b : Stored p t (n:=n) (d:=d)) (ha : Valid vars u J a) (hb : Good vars u J b) :
    Good vars u J (addStored p t M cache a b) := by
  exact ⟨Normalize.run_preserves_keys p t M cache (Product.ValidKey vars u J) a b ha hb.1,
    Normalize.run_nodup p t M cache a b hb.2⟩

theorem mul_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ) (a b : Stored p t (n:=n) (d:=d))
    (ha : Valid vars u J a) (hb : Valid vars u J b) :
    Good vars u J (mulStored p t M cache table u J a b) := by
  exact ⟨Product.run_valid p t M cache table vars u J a b [] ha hb (valid_nil vars u J),
    Product.run_nodup p t M cache table u J a b [] (by simp [Squarefree.Sparse.keys])⟩

theorem triple_good (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (h : Stored p t (n:=n) (d:=d)) (hh : Valid vars u J h)
    (v : Triple (RingProgram.ScalarCode p t)) :
    Good vars u J (tripleStored p t M cache table u J h v) := by
  have hc := constant_good (d:=d) cache vars u J hu hJ v.c
  have hb := constant_good (d:=d) cache vars u J hu hJ v.b
  have ha := constant_good (d:=d) cache vars u J hu hJ v.a
  have hch := mul_good M cache table vars u J _ h hc.1 hh
  have hchb := add_good M cache vars u J _ _ hch.1 hb
  have hchbh := mul_good M cache table vars u J _ h hchb.1 hh
  exact add_good M cache vars u J _ _ hchbh.1 ha

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
