import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsEnumeration

namespace OAI.Algorithms

/-! The exact native neutral ID is the rank of its uncovered original owner.
This is an explicit indexing equivalence, not just equality of cardinalities. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput LeafStatisticsProgram HighIncidence

theorem free_mem_lowOwners (mask : List Bool) (v : Free mask) :
    v.val.val ∈ lowOwners 0 mask := by
  apply (lowOwners_mem 0 v.val.val mask).mpr
  exact ⟨v.val, by simp, free_bit mask v⟩

theorem uncovered_owner_mem (scopes : List (List ℕ)) (mask : List Bool)
    (v : uncovered (residualScope scopes mask)) :
    v.val.val.val ∈ neutralOwners scopes 0 mask := by
  apply (neutralOwners_mem scopes 0 _ mask).mpr
  refine ⟨free_mem_lowOwners mask v.val, ?_⟩
  have hd : Incidence.degree (residualScope scopes mask) v.val = 0 :=
    (Finset.mem_filter.mp v.property).2
  rw [residual_degree] at hd
  exact List.length_eq_zero_iff.mp hd

/-- The `j`th neutral factor is attached to the `j`th uncovered free owner. -/
def neutralAt (scopes : List (List ℕ)) (mask : List Bool)
    (j : Fin (neutralOwners scopes 0 mask).length) :
    uncovered (residualScope scopes mask) := by
  let u := (neutralOwners scopes 0 mask).get j
  have hm := (neutralOwners_mem scopes 0 u mask).mp (List.get_mem _ j)
  have hb := (lowOwners_bounds 0 u mask hm.1).2
  have hu : u < mask.length := by simpa using hb
  have hf : mask.get ⟨u, hu⟩ = false := by
    obtain ⟨i, hi, hbit⟩ := (lowOwners_mem 0 u mask).mp hm.1
    have he : (⟨u, hu⟩ : Fin mask.length) = i := by
      apply Fin.ext
      simpa using hi.symm
    simpa only [he] using hbit
  let v : Free mask := ⟨⟨u, hu⟩, by rw [mem_highMask, hf]; decide⟩
  refine ⟨v, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [residual_degree]
  change (Scan.indices scopes u).length = 0
  simp [hm.2]

@[simp] theorem neutralAt_value (scopes : List (List ℕ)) (mask : List Bool)
    (j : Fin (neutralOwners scopes 0 mask).length) :
    (neutralAt scopes mask j).val.val.val = (neutralOwners scopes 0 mask).get j := rfl

def neutralIndex (scopes : List (List ℕ)) (mask : List Bool)
    (v : uncovered (residualScope scopes mask)) :
    Fin (neutralOwners scopes 0 mask).length :=
  ⟨(neutralOwners scopes 0 mask).idxOf v.val.val.val,
    List.idxOf_lt_length_iff.mpr (uncovered_owner_mem scopes mask v)⟩

def neutralOwnerEquiv (scopes : List (List ℕ)) (mask : List Bool) :
    Fin (neutralOwners scopes 0 mask).length ≃ uncovered (residualScope scopes mask) where
  toFun := neutralAt scopes mask
  invFun := neutralIndex scopes mask
  left_inv j := by
    apply Fin.ext
    change (neutralOwners scopes 0 mask).idxOf ((neutralOwners scopes 0 mask).get j) = j.val
    simpa only [List.get_eq_getElem] using
      (neutralOwners_nodup scopes 0 mask).idxOf_getElem j.val j.isLt
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    change (neutralOwners scopes 0 mask).get (neutralIndex scopes mask v) = v.val.val.val
    exact List.getElem_idxOf (neutralIndex scopes mask v).isLt

theorem factorCount_eq (scopes : List (List ℕ)) (mask : List Bool) :
    Semantics.factorCount scopes mask = scopes.length + (neutralOwners scopes 0 mask).length :=
  counter_eq_numbered_length scopes mask 0 scopes.length

/-- Encode a semantic factor by its actual native ID: original IDs are retained,
and an uncovered owner gets `q + idxOf owner` in the forward owner list. -/
def factorCodeEquiv (scopes : List (List ℕ)) (mask : List Bool) :
    (Fin scopes.length ⊕ uncovered (residualScope scopes mask)) ≃
      Fin (Semantics.factorCount scopes mask) :=
  ((Equiv.sumCongr (Equiv.refl _) (neutralOwnerEquiv scopes mask).symm).trans
    finSumFinEquiv).trans (finCongr (factorCount_eq scopes mask).symm)

@[simp] theorem factorCode_original_value (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length) :
    (factorCodeEquiv scopes mask (Sum.inl e)).val = e.val := rfl

@[simp] theorem factorCode_neutral_value (scopes : List (List ℕ)) (mask : List Bool)
    (v : uncovered (residualScope scopes mask)) :
    (factorCodeEquiv scopes mask (Sum.inr v)).val =
      scopes.length + (neutralOwners scopes 0 mask).idxOf v.val.val.val := rfl

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
