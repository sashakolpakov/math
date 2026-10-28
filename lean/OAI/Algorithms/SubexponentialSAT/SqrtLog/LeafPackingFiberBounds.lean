import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemanticsTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramPositivity

namespace OAI.Algorithms

/-! Raw native incidence records have no repeated owner-factor pair. Hence their
index fibers are bounded by the statistics of the actual completed scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
open PackingIncidenceInput LeafStatisticsSemantics LeafStatisticsProgram

 theorem factors_nodup (scopes : List (List ℕ)) (v z : ℕ) :
    (Step.factors scopes v z).Nodup := by
  by_cases h : Scan.indices scopes v = []
  · simp [Step.factors,h]
  · simp only [Step.factors,ite_eq_right h]
    exact Subexp.IncidencePlanSpec.incidentIndices_nodup scopes v

 theorem entries_nodup (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z, (Semantics.entries scopes v z mask).Nodup := by
  induction mask with
  | nil => intros; simp [Semantics.entries]
  | cons b bs ih =>
    intro v z
    cases b
    · simp only [Semantics.entries,Bool.false_eq_true,ite_false]
      apply List.nodup_append.mpr
      refine ⟨ih _ _, (factors_nodup scopes v z).map (fun x y h => Prod.mk.inj h |>.2), ?_⟩
      intro p hp q hq hpq
      subst q
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hq
      have hh := lowOwners_bounds (v+1) v bs
        (entries_owner_low scopes bs (v+1) (Step.next scopes v z) v e hp)
      omega
    · simpa [Semantics.entries] using ih (v+1) z

 theorem nativeEntries_nodup (scopes : List (List ℕ)) (mask : List Bool) :
    (Semantics.nativeEntries scopes mask).Nodup := entries_nodup scopes mask 0 scopes.length

 theorem native_get_injective (scopes : List (List ℕ)) (mask : List Bool) :
    Function.Injective (Semantics.nativeEntries scopes mask).get :=
  List.nodup_iff_injective_get.mp (nativeEntries_nodup scopes mask)

 theorem owner_low (scopes : List (List ℕ)) (mask : List Bool)
    (i : Semantics.Incidences scopes mask) :
    ((Semantics.nativeEntries scopes mask).get i).1 ∈ lowOwners 0 mask :=
  entries_owner_low scopes mask 0 scopes.length _ _ (List.get_mem _ i)

 def freeOwner (scopes : List (List ℕ)) (mask : List Bool)
    (i : Semantics.Incidences scopes mask) : Free mask :=
  ⟨⟨((Semantics.nativeEntries scopes mask).get i).1,
    by have h := (lowOwners_bounds 0 _ mask (owner_low scopes mask i)).2; omega⟩,
    by
      obtain ⟨j,hj,hb⟩ := (lowOwners_mem 0 _ mask).mp (owner_low scopes mask i)
      have he : j = ⟨((Semantics.nativeEntries scopes mask).get i).1,
        by have h := (lowOwners_bounds 0 _ mask (owner_low scopes mask i)).2; omega⟩ :=
        Fin.ext (by simpa using hj)
      simp only [mem_highMask]
      rw [← he,hb]
      decide⟩

 theorem freeOwner_mem (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (i : Semantics.Incidences scopes mask) :
    freeOwner scopes mask i ∈ nativeScope scopes mask (Semantics.factor scopes n mask hm i) := by
  rw [mem_nativeScope]
  exact List.get_mem _ i

 theorem pair_injective (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (i j : Semantics.Incidences scopes mask)
    (ho : Semantics.owner scopes n mask hm i = Semantics.owner scopes n mask hm j)
    (hf : Semantics.factor scopes n mask hm i = Semantics.factor scopes n mask hm j) : i=j := by
  apply native_get_injective scopes mask
  apply Prod.ext
  · exact congrArg Fin.val ho
  · exact congrArg Fin.val hf

 theorem free_pair_injective (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (i j : Semantics.Incidences scopes mask)
    (ho : freeOwner scopes mask i = freeOwner scopes mask j)
    (hf : Semantics.factor scopes n mask hm i = Semantics.factor scopes n mask hm j) : i=j := by
  apply native_get_injective scopes mask
  apply Prod.ext
  · exact congrArg (fun v : Free mask => v.val.val) ho
  · exact congrArg Fin.val hf

 theorem owner_fiber_le (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (v : Fin n) :
    (Finset.univ.filter fun i : Semantics.Incidences scopes mask =>
      Semantics.owner scopes n mask hm i=v).card ≤ (measured scopes mask).occurrence := by
  classical
  let s := Finset.univ.filter fun i : Semantics.Incidences scopes mask =>
    Semantics.owner scopes n mask hm i=v
  change s.card ≤ _
  by_cases hs : s.Nonempty
  · obtain ⟨j,hj⟩ := hs
    let w := freeOwner scopes mask j
    have hjv : Semantics.owner scopes n mask hm j=v := (Finset.mem_filter.mp hj).2
    have hsame (i) (hi : i ∈ s) : freeOwner scopes mask i=w := by
      apply Subtype.ext
      apply Fin.ext
      change ((Semantics.nativeEntries scopes mask).get i).1 =
        ((Semantics.nativeEntries scopes mask).get j).1
      exact congrArg Fin.val ((Finset.mem_filter.mp hi).2.trans hjv.symm)
    have hcard : s.card ≤ Incidence.degree (nativeScope scopes mask) w := by
      apply Finset.card_le_card_of_injOn (Semantics.factor scopes n mask hm)
      · intro i hi
        change _ ∈ Finset.univ.filter (fun e => w ∈ nativeScope scopes mask e)
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hsame i hi]
        exact freeOwner_mem scopes mask n hm i
      · intro i hi j hj he
        exact free_pair_injective scopes mask n hm i j ((hsame i hi).trans (hsame j hj).symm) he
    have hbound := (totals_occurrence_le_iff scopes 0 mask zero
      (measured scopes mask).occurrence).mp (le_refl (measured scopes mask).occurrence)
    rw [nativeScope_degree] at hcard
    exact hcard.trans (by simpa only [Nat.zero_add] using hbound.2 w.val (free_bit mask w))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

 theorem factor_fiber_le_scope (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (e : Fin (Semantics.factorCount scopes mask)) :
    (Finset.univ.filter fun i : Semantics.Incidences scopes mask =>
      Semantics.factor scopes n mask hm i=e).card ≤ (nativeScope scopes mask e).card := by
  classical
  apply Finset.card_le_card_of_injOn (freeOwner scopes mask)
  · intro i hi
    rw [← (Finset.mem_filter.mp hi).2]
    exact freeOwner_mem scopes mask n hm i
  · intro i hi j hj he
    exact free_pair_injective scopes mask n hm i j he
      ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

 theorem factor_fiber_le (scopes : List (List ℕ)) (mask : List Bool) (n : ℕ)
    (hm : mask.length ≤ n) (hd : ∀ row ∈ scopes, row.Nodup)
    (e : Fin (Semantics.factorCount scopes mask)) :
    (Finset.univ.filter fun i : Semantics.Incidences scopes mask =>
      Semantics.factor scopes n mask hm i=e).card ≤
      max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered=0 then 0 else 1) := by
  classical
  apply (factor_fiber_le_scope scopes mask n hm e).trans
  rw [measured,completed_arity_exact mask scopes hd]
  obtain ⟨f,rfl⟩ := (factorCodeEquiv scopes mask).surjective e
  rw [nativeScope_transport]
  exact Finset.le_sup (f := fun f => (completedScope scopes mask f).card) (Finset.mem_univ _)

end SubexponentialSAT.SqrtLog.LeafPackingFiberBounds

end OAI.Algorithms
