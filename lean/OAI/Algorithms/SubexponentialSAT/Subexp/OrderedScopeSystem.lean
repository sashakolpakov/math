import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.IncidencePlanSpec
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

namespace OAI.Algorithms

/-!
# Factor systems indexed by their emitted scope-list positions

The finite factor enumeration gives the physical factor IDs. The system
below has exactly the pattern read by the incidence-plan producer and the
original factor tables, transported along that enumeration. Its factor
count and satisfying assignments agree with the original system.
-/

namespace SubexponentialSAT.Subexp.OrderedScopeSystem

open Factor SlotAssignment ConstructivePacking

variable {D : ℕ} {F A : Type*} [DecidableEq F]

def rawScopes (factors : FiniteEnumeration F) (scopeLists : F → List (Fin D)) :
    List (List ℕ) := factors.values.map fun e => (scopeLists e).map Fin.val

omit [DecidableEq F] in
@[simp] theorem rawScopes_length (factors : FiniteEnumeration F)
    (scopeLists : F → List (Fin D)) :
    (rawScopes factors scopeLists).length = factors.values.length := by
  simp [rawScopes]

/-- The physical factor ID is its position in the actual supplied order. -/
def factorEquiv (factors : FiniteEnumeration F) (scopeLists : F → List (Fin D)) :
    Fin (rawScopes factors scopeLists).length ≃ F :=
  (finCongr (rawScopes_length factors scopeLists)).trans factors.equivFin

theorem rawScopes_get (factors : FiniteEnumeration F) (scopeLists : F → List (Fin D))
    (i : Fin (rawScopes factors scopeLists).length) :
    (rawScopes factors scopeLists).get i =
      (scopeLists (factorEquiv factors scopeLists i)).map Fin.val := by
  let j : Fin factors.values.length := ⟨i.val, by simpa [rawScopes] using i.isLt⟩
  have hij : (finCongr (rawScopes_length factors scopeLists)) i = j := by
    apply Fin.ext
    rfl
  rw [factorEquiv, Equiv.trans_apply, hij]
  rw [List.get_eq_getElem]
  simp only [rawScopes, List.getElem_map]
  change (scopeLists factors.values[i.val]).map Fin.val =
    (scopeLists (factors.values.get j)).map Fin.val
  rw [List.get_eq_getElem]

variable (S : System (Fin D) F A) (factors : FiniteEnumeration F)
  (scopeLists : F → List (Fin D))
  (scopeMem : ∀ e v, v ∈ scopeLists e ↔ v ∈ S.scope e)

include scopeMem

theorem scope_iff (i : Fin (rawScopes factors scopeLists).length) (v : Fin D) :
    v ∈ (IncidencePlanSpec.pattern D (rawScopes factors scopeLists)).scope i ↔
      v ∈ S.scope (factorEquiv factors scopeLists i) := by
  rw [IncidencePlanSpec.mem_pattern_scope, rawScopes_get]
  constructor
  · intro h
    obtain ⟨u, hu, huv⟩ := List.mem_map.mp h
    have heq : u = v := Fin.ext huv
    exact (scopeMem _ v).mp (heq ▸ hu)
  · intro h
    exact List.mem_map.mpr ⟨v, (scopeMem _ v).mpr h, rfl⟩

/-- Numeric scopes and the original tables in the same physical factor order. -/
def system : System (Fin D) (Fin (rawScopes factors scopeLists).length) A where
  scope := (IncidencePlanSpec.pattern D (rawScopes factors scopeLists)).scope
  table i x := S.table (factorEquiv factors scopeLists i)
    (fun v => x ⟨v.val, (scope_iff S factors scopeLists scopeMem i v.val).mpr v.property⟩)

@[simp] theorem system_toPattern :
    (system S factors scopeLists scopeMem).toPattern =
      IncidencePlanSpec.pattern D (rawScopes factors scopeLists) := rfl

@[simp] theorem evalFactor_system (i : Fin (rawScopes factors scopeLists).length)
    (x : Fin D → A) :
    evalFactor (system S factors scopeLists scopeMem) i x =
      evalFactor S (factorEquiv factors scopeLists i) x := rfl

theorem scopeLists_mem (i : Fin (rawScopes factors scopeLists).length) (v : Fin D) :
    v ∈ scopeLists (factorEquiv factors scopeLists i) ↔
      v ∈ (system S factors scopeLists scopeMem).scope i :=
  (scopeMem _ v).trans (scope_iff S factors scopeLists scopeMem i v).symm

theorem satisfies_system (x : Fin D → A) :
    Satisfies (system S factors scopeLists scopeMem) x ↔ Satisfies S x := by
  constructor
  · intro h e
    have he := h ((factorEquiv factors scopeLists).symm e)
    simpa using he
  · intro h i
    exact h (factorEquiv factors scopeLists i)

/-- Incidence is preserved by the same physical-factor equivalence. -/
def incidentEquiv (v : Fin D) :
    Incident (system S factors scopeLists scopeMem).toPattern v ≃ Incident S.toPattern v where
  toFun i := ⟨factorEquiv factors scopeLists i.val,
    (scope_iff S factors scopeLists scopeMem i.val v).mp i.property⟩
  invFun e := ⟨(factorEquiv factors scopeLists).symm e.val,
    (scope_iff S factors scopeLists scopeMem _ v).mpr (by simpa using e.property)⟩
  left_inv i := by apply Subtype.ext; exact (factorEquiv factors scopeLists).symm_apply_apply i.val
  right_inv e := by apply Subtype.ext; exact (factorEquiv factors scopeLists).apply_symm_apply e.val

variable [Fintype F]

theorem bounded {k Δ : ℕ} (hP : S.toPattern.Bounded k Δ) :
    (system S factors scopeLists scopeMem).toPattern.Bounded k Δ := by
  have hs (i : Fin (rawScopes factors scopeLists).length) :
      (system S factors scopeLists scopeMem).scope i =
        S.scope (factorEquiv factors scopeLists i) := by
    ext v
    exact scope_iff S factors scopeLists scopeMem i v
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hs]
    exact hP.nonempty_scope _
  · intro i
    rw [hs]
    exact hP.arity_le _
  · intro v
    rw [← card_incident]
    rw [Fintype.card_congr (incidentEquiv S factors scopeLists scopeMem v)]
    exact card_incident_le S.toPattern hP v

theorem degree_le {k Δ : ℕ} (hP : S.toPattern.Bounded k Δ) (v : Fin D) :
    IncidencePlanSpec.degree (rawScopes factors scopeLists) v.val ≤ Δ :=
  IncidencePlanSpec.degree_le_of_bounded D k Δ (rawScopes factors scopeLists)
    (bounded S factors scopeLists scopeMem hP) v

/-- The supplied factor order determines the slots; no SlotMap is an input. -/
def slots {k Δ : ℕ} (hP : S.toPattern.Bounded k Δ) :
    SlotMap (system S factors scopeLists scopeMem).toPattern Δ :=
  IncidencePlanSpec.slots D Δ (rawScopes factors scopeLists)
    (degree_le S factors scopeLists scopeMem hP)

theorem vertexPlan_eq_readPlan {k Δ : ℕ} (hP : S.toPattern.Bounded k Δ) (v : Fin D) :
    IncidencePlanSpec.vertexPlan D Δ (rawScopes factors scopeLists) v.val =
      ReadPlan.vertexPlan (system S factors scopeLists scopeMem).toPattern
        (slots S factors scopeLists scopeMem hP) (List.finRange D)
        (List.finRange (rawScopes factors scopeLists).length) v :=
  IncidencePlanSpec.vertexPlan_eq_readPlan D Δ (rawScopes factors scopeLists)
    (degree_le S factors scopeLists scopeMem hP) v

theorem producedPlan_eq_readPlan_reverse {k Δ : ℕ} (hP : S.toPattern.Bounded k Δ) (v : Fin D) :
    IncidencePlanSpec.producedPlan D Δ (rawScopes factors scopeLists) v.val =
      (ReadPlan.vertexPlan (system S factors scopeLists scopeMem).toPattern
        (slots S factors scopeLists scopeMem hP) (List.finRange D)
        (List.finRange (rawScopes factors scopeLists).length) v).reverse :=
  congrArg List.reverse (vertexPlan_eq_readPlan S factors scopeLists scopeMem hP v)

/-- Reindexing factors preserves the actual finite sum-of-products count. -/
theorem count_system [Fintype A] :
    count (system S factors scopeLists scopeMem) = count S := by
  unfold count
  apply Finset.sum_congr rfl
  intro x _
  simp only [weight_eq_indicator, satisfies_system S factors scopeLists scopeMem]

end SubexponentialSAT.Subexp.OrderedScopeSystem

end OAI.Algorithms
