import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputSemantics

namespace OAI.Algorithms

/-! Exact owner order of the neutral factors emitted by the native scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput

/-- Free owners in increasing original-coordinate order. -/
def lowOwners : ℕ → List Bool → List ℕ
  | _, [] => []
  | v, high :: rest => if high then lowOwners (v+1) rest else v :: lowOwners (v+1) rest

/-- Uncovered free owners in the order in which the native counter advances. -/
def neutralOwners (scopes : List (List ℕ)) : ℕ → List Bool → List ℕ
  | _, [] => []
  | v, high :: rest =>
      if high then neutralOwners scopes (v+1) rest
      else if Scan.indices scopes v = [] then v :: neutralOwners scopes (v+1) rest
      else neutralOwners scopes (v+1) rest

/-- The actual original-factor incidence pairs; owner blocks may be reversed. -/
def originalPairs (scopes : List (List ℕ)) : ℕ → List Bool → List (ℕ × ℕ)
  | _, [] => []
  | v, high :: rest => originalPairs scopes (v+1) rest ++
      if high then [] else (Scan.indices scopes v).map fun e => (v,e)

/-- Forward numbering is independent of the reversed order of emitted records. -/
def numbered : ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | z, v :: rest => (v,z) :: numbered (z+1) rest

theorem lowOwners_mem (v u : ℕ) (mask : List Bool) :
    u ∈ lowOwners v mask ↔
      ∃ i : Fin mask.length, v+i.val = u ∧ mask.get i = false := by
  induction mask generalizing v with
  | nil => simp [lowOwners]
  | cons b bs ih =>
    constructor
    · intro h
      cases b
      · change u ∈ v :: lowOwners (v+1) bs at h
        rcases List.mem_cons.mp h with h | h
        · refine ⟨⟨0, by simp⟩, ?_, rfl⟩
          simpa only [Fin.val_zero, Nat.add_zero] using h.symm
        · obtain ⟨i, hi, hb⟩ := (ih (v+1)).mp h
          refine ⟨i.succ, ?_, hb⟩
          simp only [Fin.val_succ]
          omega
      · change u ∈ lowOwners (v+1) bs at h
        obtain ⟨i, hi, hb⟩ := (ih (v+1)).mp h
        refine ⟨i.succ, ?_, hb⟩
        simp only [Fin.val_succ]
        omega
    · rintro ⟨i, hi, hb⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · have hb' : b = false := hb
        subst b
        change u ∈ v :: lowOwners (v+1) bs
        apply List.mem_cons.mpr
        left
        simpa only [Fin.val_zero, Nat.add_zero] using hi.symm
      · have hj : (v+1)+j.val = u := by
          simp only [Fin.val_succ] at hi
          omega
        have hg : bs.get j = false := hb
        have hm := (ih (v+1)).mpr ⟨j, hj, hg⟩
        cases b
        · exact List.mem_cons_of_mem v hm
        · exact hm

theorem lowOwners_bounds (v u : ℕ) (mask : List Bool) (hu : u ∈ lowOwners v mask) :
    v ≤ u ∧ u < v+mask.length := by
  obtain ⟨i, hi, _⟩ := (lowOwners_mem v u mask).mp hu
  have := i.isLt
  omega

theorem lowOwners_nodup (v : ℕ) (mask : List Bool) : (lowOwners v mask).Nodup := by
  induction mask generalizing v with
  | nil => simp [lowOwners]
  | cons b bs ih =>
    have hn : v ∉ lowOwners (v+1) bs := by
      intro hv
      have := (lowOwners_bounds (v+1) v bs hv).1
      omega
    cases b <;> simp [lowOwners, ih, hn]

theorem neutralOwners_eq_filter (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) :
    neutralOwners scopes v mask =
      (lowOwners v mask).filter (fun u => decide (Scan.indices scopes u = [])) := by
  induction mask generalizing v with
  | nil => simp [neutralOwners, lowOwners]
  | cons b bs ih =>
    cases b <;> by_cases h : Scan.indices scopes v = [] <;>
      simp [neutralOwners, lowOwners, ih, h]

theorem neutralOwners_mem (scopes : List (List ℕ)) (v u : ℕ) (mask : List Bool) :
    u ∈ neutralOwners scopes v mask ↔ u ∈ lowOwners v mask ∧ Scan.indices scopes u = [] := by
  simp [neutralOwners_eq_filter]

theorem neutralOwners_nodup (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) :
    (neutralOwners scopes v mask).Nodup := by
  rw [neutralOwners_eq_filter]
  exact (lowOwners_nodup v mask).filter _

theorem originalPairs_mem (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v u e, (u,e) ∈ originalPairs scopes v mask ↔
      u ∈ lowOwners v mask ∧ e ∈ Scan.indices scopes u := by
  induction mask with
  | nil => intros; simp [originalPairs, lowOwners]
  | cons b bs ih =>
    intro v u e
    cases b <;> by_cases hu : u = v
    all_goals simp [originalPairs, lowOwners, ih, hu]
    all_goals exact fun _ h => False.elim (hu h.symm)

theorem entries_mem_split (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z p, p ∈ Semantics.entries scopes v z mask ↔
      p ∈ originalPairs scopes v mask ∨ p ∈ numbered z (neutralOwners scopes v mask) := by
  induction mask with
  | nil => intros; simp [Semantics.entries, originalPairs, numbered, neutralOwners]
  | cons b bs ih =>
    intro v z p
    cases b <;> by_cases h : Scan.indices scopes v = [] <;>
      simp [Semantics.entries, originalPairs, numbered, neutralOwners, Step.next,
        Step.factors, h, ih, or_assoc, or_comm]

theorem counter_eq_numbered_length (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z, Loop.finalCounter scopes v z mask = z + (neutralOwners scopes v mask).length := by
  induction mask with
  | nil => intros; simp [Loop.finalCounter, neutralOwners]
  | cons b bs ih =>
    intro v z
    cases b <;> by_cases h : Scan.indices scopes v = [] <;>
      simp [Loop.finalCounter, neutralOwners, Step.next, h, ih, Nat.add_assoc,
        Nat.add_comm]

theorem numbered_mem (owners : List ℕ) :
    ∀ z u e, (u,e) ∈ numbered z owners ↔
      ∃ i : Fin owners.length, owners.get i = u ∧ z+i.val = e := by
  induction owners with
  | nil => intros; simp [numbered]
  | cons v vs ih =>
    intro z u e
    simp [numbered, ih, Fin.exists_fin_succ, Nat.add_comm,
      Nat.add_left_comm, eq_comm, and_comm]

theorem numbered_factor_ge (owners : List ℕ) (z u e : ℕ)
    (hp : (u,e) ∈ numbered z owners) : z ≤ e := by
  obtain ⟨i, _, hi⟩ := (numbered_mem owners z u e).mp hp
  omega

theorem native_original_mem (scopes : List (List ℕ)) (mask : List Bool)
    (v z u e : ℕ) (hz : scopes.length ≤ z) (he : e < scopes.length) :
    (u,e) ∈ Semantics.entries scopes v z mask ↔
      u ∈ lowOwners v mask ∧ e ∈ Scan.indices scopes u := by
  rw [entries_mem_split, originalPairs_mem]
  have hn : (u,e) ∉ numbered z (neutralOwners scopes v mask) := by
    intro hp
    have := numbered_factor_ge (neutralOwners scopes v mask) z u e hp
    omega
  simp [hn]

theorem native_neutral_mem (scopes : List (List ℕ)) (mask : List Bool)
    (v z u e : ℕ) (hz : scopes.length ≤ z) (he : z ≤ e) :
    (u,e) ∈ Semantics.entries scopes v z mask ↔
      ∃ i : Fin (neutralOwners scopes v mask).length,
        (neutralOwners scopes v mask).get i = u ∧ z+i.val = e := by
  rw [entries_mem_split, numbered_mem]
  have hn : (u,e) ∉ originalPairs scopes v mask := by
    intro hp
    have hi := ((originalPairs_mem scopes mask v u e).mp hp).2
    have := Subexp.IncidencePlanSpec.incidentIndex_lt scopes u e hi
    omega
  simp [hn]

theorem entries_owner_low (scopes : List (List ℕ)) (mask : List Bool)
    (v z u e : ℕ) (h : (u,e) ∈ Semantics.entries scopes v z mask) :
    u ∈ lowOwners v mask := by
  rcases (entries_mem_split scopes mask v z (u,e)).mp h with ho | hn
  · exact ((originalPairs_mem scopes mask v u e).mp ho).1
  · obtain ⟨i, hi, _⟩ := (numbered_mem (neutralOwners scopes v mask) z u e).mp hn
    have hu := List.get_mem (neutralOwners scopes v mask) i
    rw [hi] at hu
    exact ((neutralOwners_mem scopes v u mask).mp hu).1

theorem native_no_high_owner (scopes : List (List ℕ)) (mask : List Bool)
    (u : Fin mask.length) (hu : mask.get u = true) (e : ℕ) :
    (u.val,e) ∉ Semantics.nativeEntries scopes mask := by
  intro h
  obtain ⟨i, hi, hb⟩ := (lowOwners_mem 0 u.val mask).mp
    (entries_owner_low scopes mask 0 scopes.length u.val e h)
  have he : i = u := by apply Fin.ext; simpa using hi
  subst i
  simp only [List.get_eq_getElem] at hu
  simp [hu] at hb

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
