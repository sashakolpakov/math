import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan
import OAI.Algorithms.SubexponentialSAT.Subexp.SeedIndexFormulas

namespace OAI.Algorithms

/-!
# Ordered incidence plans from finite scope lists

The numeric producer records incident factors in their input order. The
typed refinement uses the rank in that same list as the local slot.
-/

namespace SubexponentialSAT.Subexp.IncidencePlanSpec

/-- Record incident factor positions while advancing through the scope list. -/
def incidenceFrom (v start : ℕ) : List (List ℕ) → List ℕ
  | [] => []
  | C :: Cs =>
      if v ∈ C then start :: incidenceFrom v (start + 1) Cs
      else incidenceFrom v (start + 1) Cs

def incidentIndices (scopes : List (List ℕ)) (v : ℕ) : List ℕ :=
  incidenceFrom v 0 scopes

def degree (scopes : List (List ℕ)) (v : ℕ) : ℕ :=
  (incidentIndices scopes v).length

/-- Head seed, incident factor seeds, then private unused-slot seeds. -/
def vertexPlan (D Δ : ℕ) (scopes : List (List ℕ)) (v : ℕ) : List ℕ :=
  (scopes.length + v) ::
    (incidentIndices scopes v ++
      List.range' (scopes.length + D + v * Δ + degree scopes v) (Δ - degree scopes v))

/-- The stack producer emits this reverse order. -/
def producedPlan (D Δ : ℕ) (scopes : List (List ℕ)) (v : ℕ) : List ℕ :=
  (vertexPlan D Δ scopes v).reverse

theorem vertexPlan_length (D Δ : ℕ) (scopes : List (List ℕ)) (v : ℕ)
    (hd : degree scopes v ≤ Δ) :
    (vertexPlan D Δ scopes v).length = Δ + 1 := by
  simp only [vertexPlan, List.length_cons, List.length_append, List.length_range', degree] at *
  omega

theorem producedPlan_eq (D Δ : ℕ) (scopes : List (List ℕ)) (v : ℕ) :
    producedPlan D Δ scopes v =
      (List.range' (scopes.length + D + v * Δ + degree scopes v)
        (Δ - degree scopes v)).reverse ++
      (incidentIndices scopes v).reverse ++ [scopes.length + v] := by
  simp [producedPlan, vertexPlan, List.reverse_append, List.append_assoc]

theorem mem_incidenceFrom (v start e : ℕ) (scopes : List (List ℕ)) :
    e ∈ incidenceFrom v start scopes ↔
      ∃ i : Fin scopes.length, start + i.val = e ∧ v ∈ scopes.get i := by
  induction scopes generalizing start with
  | nil => simp [incidenceFrom]
  | cons C Cs ih =>
    by_cases hv : v ∈ C
    · simp [incidenceFrom, hv, ih, Fin.exists_fin_succ,
        Nat.add_comm, Nat.add_left_comm, eq_comm]
    · simp [incidenceFrom, hv, ih, Fin.exists_fin_succ,
        Nat.add_comm, Nat.add_left_comm, eq_comm]

theorem incidenceFrom_bounds (v start e : ℕ) (scopes : List (List ℕ))
    (he : e ∈ incidenceFrom v start scopes) :
    start ≤ e ∧ e < start + scopes.length := by
  obtain ⟨i, hi, _⟩ := (mem_incidenceFrom v start e scopes).mp he
  have := i.isLt
  omega

theorem incidenceFrom_nodup (v start : ℕ) (scopes : List (List ℕ)) :
    (incidenceFrom v start scopes).Nodup := by
  induction scopes generalizing start with
  | nil => simp [incidenceFrom]
  | cons C Cs ih =>
    by_cases hv : v ∈ C
    · simp only [incidenceFrom, ite_eq_left hv, List.nodup_cons]
      refine ⟨?_, ih (start + 1)⟩
      intro h
      have := incidenceFrom_bounds v (start + 1) start Cs h
      omega
    · simpa only [incidenceFrom, ite_eq_right hv] using ih (start + 1)

theorem incidentIndices_nodup (scopes : List (List ℕ)) (v : ℕ) :
    (incidentIndices scopes v).Nodup :=
  incidenceFrom_nodup v 0 scopes

theorem mem_incidentIndices (scopes : List (List ℕ)) (v : ℕ) (e : Fin scopes.length) :
    e.val ∈ incidentIndices scopes v ↔ v ∈ scopes.get e := by
  rw [incidentIndices, mem_incidenceFrom]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨i, hi, hv⟩
    have : i = e := Fin.ext hi
    simpa only [this] using hv
  · intro hv
    exact ⟨e, rfl, hv⟩

theorem incidentIndex_lt (scopes : List (List ℕ)) (v e : ℕ)
    (he : e ∈ incidentIndices scopes v) : e < scopes.length := by
  have h := (incidenceFrom_bounds v 0 e scopes he).2
  simpa only [Nat.zero_add] using h

/-- The finite typed pattern obtained by testing membership in the actual
scope lists. Repeated entries and their inner order do not change incidence. -/
def pattern (D : ℕ) (scopes : List (List ℕ)) :
    SubexponentialSAT.Factor.Pattern (Fin D) (Fin scopes.length) where
  scope e := Finset.univ.filter fun v => v.val ∈ scopes.get e

@[simp] theorem mem_pattern_scope (D : ℕ) (scopes : List (List ℕ))
    (v : Fin D) (e : Fin scopes.length) :
    v ∈ (pattern D scopes).scope e ↔ v.val ∈ scopes.get e := by
  simp [pattern]

open SubexponentialSAT.SlotAssignment

theorem incident_mem (D : ℕ) (scopes : List (List ℕ)) (v : Fin D)
    (e : Incident (pattern D scopes) v) :
    e.val.val ∈ incidentIndices scopes v.val :=
  (mem_incidentIndices scopes v.val e.val).mpr
    ((mem_pattern_scope D scopes v e.val).mp e.property)

/-- Lookup by occurrence rank in the list emitted by the numeric producer. -/
def incidentAt (D : ℕ) (scopes : List (List ℕ)) (v : Fin D)
    (i : Fin (degree scopes v.val)) : Incident (pattern D scopes) v := by
  let e := (incidentIndices scopes v.val).get i
  have he : e ∈ incidentIndices scopes v.val := List.get_mem _ _
  have hlt : e < scopes.length := incidentIndex_lt scopes v.val e he
  refine ⟨⟨e, hlt⟩, ?_⟩
  exact (mem_pattern_scope D scopes v ⟨e, hlt⟩).mpr
    ((mem_incidentIndices scopes v.val ⟨e, hlt⟩).mp he)

/-- Incident factors and their explicitly computed occurrence ranks. -/
def incidentEquiv (D : ℕ) (scopes : List (List ℕ)) (v : Fin D) :
    Incident (pattern D scopes) v ≃ Fin (degree scopes v.val) where
  toFun e := ⟨(incidentIndices scopes v.val).idxOf e.val.val,
    List.idxOf_lt_length_iff.mpr (incident_mem D scopes v e)⟩
  invFun := incidentAt D scopes v
  left_inv e := by
    apply Subtype.ext
    apply Fin.ext
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (incident_mem D scopes v e))
  right_inv i := by
    apply Fin.ext
    exact (incidentIndices_nodup scopes v.val).idxOf_getElem i.val i.isLt

theorem card_incident (D : ℕ) (scopes : List (List ℕ)) (v : Fin D) :
    Fintype.card (Incident (pattern D scopes) v) = degree scopes v.val := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (incidentEquiv D scopes v)

theorem degree_le_of_bounded (D k Δ : ℕ) (scopes : List (List ℕ))
    (hP : (pattern D scopes).Bounded k Δ) (v : Fin D) :
    degree scopes v.val ≤ Δ := by
  rw [← card_incident D scopes v]
  exact SubexponentialSAT.SlotAssignment.card_incident_le (pattern D scopes) hP v

/-- The actual rank-based slot assignment. It is constructed from scope lists,
not supplied as an arbitrary runtime object. -/
def slots (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) : SlotMap (pattern D scopes) Δ :=
  fun v => (incidentEquiv D scopes v).toEmbedding.trans (Fin.castLEEmb (hd v))

@[simp] theorem slots_val (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) (v : Fin D)
    (e : Incident (pattern D scopes) v) :
    (slots D Δ scopes hd v e).val = (incidentIndices scopes v.val).idxOf e.val.val := rfl

theorem slots_val_lt_degree (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) (v : Fin D)
    (e : Incident (pattern D scopes) v) :
    (slots D Δ scopes hd v e).val < degree scopes v.val :=
  (incidentEquiv D scopes v e).isLt

theorem slots_incidentAt (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) (v : Fin D)
    (i : Fin (degree scopes v.val)) :
    slots D Δ scopes hd v (incidentAt D scopes v i) = Fin.castLE (hd v) i := by
  apply Fin.ext
  change (incidentEquiv D scopes v (incidentAt D scopes v i)).val = i.val
  exact congrArg (fun j : Fin (degree scopes v.val) => j.val)
    ((incidentEquiv D scopes v).apply_symm_apply i)

theorem slot_used_iff (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) (v : Fin D) (i : Fin Δ) :
    (∃ e, slots D Δ scopes hd v e = i) ↔ i.val < degree scopes v.val := by
  constructor
  · rintro ⟨e, rfl⟩
    exact slots_val_lt_degree D Δ scopes hd v e
  · intro hi
    refine ⟨incidentAt D scopes v ⟨i.val, hi⟩, ?_⟩
    exact (slots_incidentAt D Δ scopes hd v ⟨i.val, hi⟩).trans (Fin.ext rfl)

theorem ofFn_padded (xs : List ℕ) (N base : ℕ) (hlen : xs.length ≤ N) :
    List.ofFn (fun i : Fin N =>
      if h : i.val < xs.length then xs.get ⟨i.val, h⟩ else base + i.val) =
      xs ++ List.range' (base + xs.length) (N - xs.length) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_range']
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn]
    by_cases h : i < xs.length
    · rw [dite_eq_left h, List.getElem_append_left h]
      rfl
    · rw [dite_eq_right h, List.getElem_append_right (Nat.le_of_not_lt h)]
      simp only [List.getElem_range' ]
      omega

open AssignmentEnumeration

theorem readHeadCode (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) (v : Fin D) :
    seedCode (List.finRange D) (List.finRange scopes.length) Δ
      (ReadPlan.readSeed (pattern D scopes) (slots D Δ scopes hd) v 0) =
        scopes.length + v.val := by
  change seedCode _ _ Δ
    (SubexponentialSAT.TypeDistribution.reads (pattern D scopes) (slots D Δ scopes hd) v (.inl ())) = _
  rw [SubexponentialSAT.TypeDistribution.reads_head, SeedIndexFormulas.headCode]

theorem readSlotCode (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) (v : Fin D) (i : Fin Δ) :
    seedCode (List.finRange D) (List.finRange scopes.length) Δ
      (ReadPlan.readSeed (pattern D scopes) (slots D Δ scopes hd) v i.succ) =
        if h : i.val < degree scopes v.val then (incidentIndices scopes v.val).get ⟨i.val, h⟩
        else scopes.length + D + v.val * Δ + i.val := by
  change seedCode _ _ Δ
    (SubexponentialSAT.TypeDistribution.reads (pattern D scopes) (slots D Δ scopes hd) v (.inr i)) = _
  by_cases hi : i.val < degree scopes v.val
  · let j : Fin (degree scopes v.val) := ⟨i.val, hi⟩
    let e := incidentAt D scopes v j
    have hs : slots D Δ scopes hd v e = i :=
      (slots_incidentAt D Δ scopes hd v j).trans (Fin.ext rfl)
    have hr : SubexponentialSAT.TypeDistribution.reads (pattern D scopes) (slots D Δ scopes hd) v
        (.inr i) = .inl e.val := by
      calc
        _ = SubexponentialSAT.TypeDistribution.reads (pattern D scopes) (slots D Δ scopes hd) v
            (.inr (slots D Δ scopes hd v e)) :=
          congrArg (fun t => SubexponentialSAT.TypeDistribution.reads (pattern D scopes)
            (slots D Δ scopes hd) v (.inr t)) hs.symm
        _ = .inl e.val := SubexponentialSAT.TypeDistribution.reads_used _ _ _ e
    rw [dite_eq_left hi, hr, SeedIndexFormulas.factorCode]
    rfl
  · have hu : ¬ ∃ e, slots D Δ scopes hd v e = i :=
      fun h => hi ((slot_used_iff D Δ scopes hd v i).mp h)
    have hr := SubexponentialSAT.TypeDistribution.reads_unused (pattern D scopes)
      (slots D Δ scopes hd) v ⟨i, hu⟩
    rw [dite_eq_right hi, hr, SeedIndexFormulas.paddingCode]

/-- The computed numeric plan is exactly the typed read plan for the explicit
occurrence-rank slot assignment. No arbitrary SlotMap is an input. -/
theorem vertexPlan_eq_readPlan (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) (v : Fin D) :
    vertexPlan D Δ scopes v.val =
      ReadPlan.vertexPlan (pattern D scopes) (slots D Δ scopes hd)
        (List.finRange D) (List.finRange scopes.length) v := by
  symm
  unfold ReadPlan.vertexPlan vertexPlan
  rw [List.ofFn_succ]
  apply congrArg₂ List.cons
  · exact readHeadCode D Δ scopes hd v
  · calc
      _ = List.ofFn (fun i : Fin Δ =>
          if h : i.val < degree scopes v.val then (incidentIndices scopes v.val).get ⟨i.val, h⟩
          else scopes.length + D + v.val * Δ + i.val) := by
        apply congrArg List.ofFn
        funext i
        exact readSlotCode D Δ scopes hd v i
      _ = _ := ofFn_padded (incidentIndices scopes v.val) Δ
        (scopes.length + D + v.val * Δ) (hd v)

theorem producedPlan_eq_readPlan_reverse (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) (v : Fin D) :
    producedPlan D Δ scopes v.val =
      (ReadPlan.vertexPlan (pattern D scopes) (slots D Δ scopes hd)
        (List.finRange D) (List.finRange scopes.length) v).reverse :=
  congrArg List.reverse (vertexPlan_eq_readPlan D Δ scopes hd v)

theorem vertexPlan_valid (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) (v : Fin D) (j : ℕ)
    (hj : j ∈ vertexPlan D Δ scopes v.val) :
    j < scopes.length + (Δ + 1) * D := by
  rw [vertexPlan_eq_readPlan D Δ scopes hd v] at hj
  have h := ReadPlan.vertexPlan_valid (pattern D scopes) (slots D Δ scopes hd)
    (List.finRange D) (List.finRange scopes.length)
    (fun v => List.mem_finRange v) (fun e => List.mem_finRange e) v j hj
  simpa only [seedIndices_length, List.length_finRange] using h

/-- Gathering the actual numeric plan recovers the same local type encoding
used by the collision selector. -/
theorem gather_vertexPlan (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, degree scopes v.val ≤ Δ) {r Q : ℕ}
    (ω : SubexponentialSAT.SubexpTypeVariance.Assignment (Fin D) (Fin scopes.length) r Q Δ)
    (v : Fin D) :
    (ReadPlan.gather []
      (ReadPlan.seedRows (List.finRange D) (List.finRange scopes.length) ω)
      (vertexPlan D Δ scopes v.val)).flatten =
        CollisionProgram.encodeType
          (SubexponentialSAT.SubexpTypeVariance.assignmentType (pattern D scopes) (slots D Δ scopes hd) ω v) := by
  rw [vertexPlan_eq_readPlan D Δ scopes hd v]
  exact ReadPlan.gather_seedRows (pattern D scopes) (slots D Δ scopes hd)
    (List.finRange D) (List.finRange scopes.length)
    (fun v => List.mem_finRange v) (fun e => List.mem_finRange e) ω v

end SubexponentialSAT.Subexp.IncidencePlanSpec

end OAI.Algorithms
