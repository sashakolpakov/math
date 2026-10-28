import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsArity

namespace OAI.Algorithms

/-! Scope transport for the actual native factor IDs. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput HighIncidence

/-- Read the scope from exactly the emitted `(original owner, native factor)`
records, retaining the original free-coordinate subtype. -/
def nativeScope (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin (Semantics.factorCount scopes mask)) : Finset (Free mask) :=
  Finset.univ.filter fun v => (v.val.val,e.val) ∈ Semantics.nativeEntries scopes mask

@[simp] theorem mem_nativeScope (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin (Semantics.factorCount scopes mask)) (v : Free mask) :
    v ∈ nativeScope scopes mask e ↔
      (v.val.val,e.val) ∈ Semantics.nativeEntries scopes mask := by
  simp [nativeScope]

theorem nativeScope_original (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length) :
    nativeScope scopes mask (factorCodeEquiv scopes mask (Sum.inl e)) =
      residualScope scopes mask e := by
  ext v
  rw [mem_nativeScope, factorCode_original_value]
  change (v.val.val,e.val) ∈ Semantics.entries scopes 0 scopes.length mask ↔ _
  rw [native_original_mem scopes mask 0 scopes.length v.val.val e.val le_rfl e.isLt]
  rw [and_iff_right (free_mem_lowOwners mask v), residual_mem]
  exact Subexp.IncidencePlanSpec.mem_incidentIndices scopes v.val.val e

theorem nativeScope_neutral (scopes : List (List ℕ)) (mask : List Bool)
    (w : uncovered (residualScope scopes mask)) :
    nativeScope scopes mask (factorCodeEquiv scopes mask (Sum.inr w)) = {w.val} := by
  ext v
  rw [mem_nativeScope, factorCode_neutral_value]
  change (v.val.val,scopes.length + (neutralOwners scopes 0 mask).idxOf w.val.val.val) ∈
      Semantics.entries scopes 0 scopes.length mask ↔ v ∈ ({w.val} : Finset (Free mask))
  rw [native_neutral_mem scopes mask 0 scopes.length _ _ le_rfl (Nat.le_add_right _ _)]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, he⟩
    have hei : i = neutralIndex scopes mask w := by
      apply Fin.ext
      change i.val = (neutralOwners scopes 0 mask).idxOf w.val.val.val
      omega
    subst i
    have hw := congrArg (fun u : uncovered (residualScope scopes mask) => u.val.val.val)
      ((neutralOwnerEquiv scopes mask).apply_symm_apply w)
    change (neutralOwners scopes 0 mask).get (neutralIndex scopes mask w) = w.val.val.val at hw
    apply Subtype.ext
    apply Fin.ext
    exact hi.symm.trans hw
  · intro hv
    subst v
    refine ⟨neutralIndex scopes mask w, ?_, rfl⟩
    have hw := congrArg (fun u : uncovered (residualScope scopes mask) => u.val.val.val)
      ((neutralOwnerEquiv scopes mask).apply_symm_apply w)
    exact hw

/-- The concrete rank-based bijection transports every native scope exactly to
the residual original factor or the singleton of its numbered uncovered owner. -/
theorem nativeScope_transport (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length ⊕ uncovered (residualScope scopes mask)) :
    nativeScope scopes mask (factorCodeEquiv scopes mask e) = completedScope scopes mask e := by
  cases e with
  | inl e => exact nativeScope_original scopes mask e
  | inr v => exact nativeScope_neutral scopes mask v

theorem nativeScope_covers (scopes : List (List ℕ)) (mask : List Bool) (v : Free mask) :
    ∃ e, v ∈ nativeScope scopes mask e := by
  obtain ⟨e, he⟩ := neutralScope_covers (residualScope scopes mask) v
  refine ⟨factorCodeEquiv scopes mask e, ?_⟩
  rw [nativeScope_transport]
  exact he

theorem nativeScope_degree (scopes : List (List ℕ)) (mask : List Bool) (v : Free mask) :
    Incidence.degree (nativeScope scopes mask) v =
      max 1 (LeafStatisticsProgram.degree scopes v.val.val) := by
  calc
    _ = Incidence.degree (completedScope scopes mask) v := by
      rw [Incidence.degree_eq_sum, Incidence.degree_eq_sum]
      symm
      apply Fintype.sum_equiv (factorCodeEquiv scopes mask)
      intro e
      rw [nativeScope_transport]
    _ = _ := completed_degree scopes mask v

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
