import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Greedy coloring with a local-cardinality bound, in a form convenient
for the sparse-ball decomposition in epsilon removal. -/
theorem finite_relation_coloring {X : Type*} (R : X → X → Prop) [DecidableRel R]
    (hsymm : ∀ ⦃x y⦄, R x y → R y x) (hirr : ∀ x, ¬ R x x) (k : ℕ) (hk : 0 < k)
    (S : Finset X)
    (hdeg : ∀ x ∈ S, (S.filter (R x)).card < k) :
    ∃ c : X → Fin k, ∀ x ∈ S, ∀ y ∈ S, R x y → c x ≠ c y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨fun _ ↦ ⟨0, hk⟩, by simp⟩
  | @insert x S hx ih =>
      have hdegS : ∀ y ∈ S, (S.filter (R y)).card < k := by
        intro y hy
        exact (Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.subset_insert x S))).trans_lt (hdeg y (Finset.mem_insert_of_mem hy))
      obtain ⟨c, hc⟩ := ih hdegS
      let used : Finset (Fin k) := (S.filter (R x)).image c
      have hu : used.card < k := (Finset.card_image_le).trans_lt
        ((Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert x S))).trans_lt
          (hdeg x (Finset.mem_insert_self x S)))
      have hex : ∃ a : Fin k, a ∉ used := by
        by_contra! h
        have he : used = Finset.univ := Finset.eq_univ_iff_forall.mpr h
        simp [he] at hu
      obtain ⟨a, ha⟩ := hex
      refine ⟨Function.update c x a, ?_⟩
      intro y hy z hz hyz
      by_cases hyx : y = x
      · subst y
        have hzx : z ≠ x := by intro he; subst z; exact hirr x hyz
        have hzS : z ∈ S := Finset.mem_of_mem_insert_of_ne hz hzx
        have hcz : c z ∈ used := Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzS, hyz⟩, rfl⟩
        simpa [Function.update_apply, hzx] using (ne_of_mem_of_not_mem hcz ha).symm
      · by_cases hzx : z = x
        · subst z
          have hyS : y ∈ S := Finset.mem_of_mem_insert_of_ne hy hyx
          have hcy : c y ∈ used := Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hyS, hsymm hyz⟩, rfl⟩
          simpa [Function.update_apply, hyx] using (ne_of_mem_of_not_mem hcy ha)
        · have hyS : y ∈ S := Finset.mem_of_mem_insert_of_ne hy hyx
          have hzS : z ∈ S := Finset.mem_of_mem_insert_of_ne hz hzx
          simpa [Function.update_apply, hyx, hzx] using hc y hyS z hzS hyz

/-- A finite set whose radius-`r` neighborhoods have fewer than `k`
other points splits into `k` families separated by at least `r`. -/
theorem finite_metric_coloring {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (S : Finset X) (r : ℝ) (k : ℕ) (hk : 0 < k)
    (hdeg : ∀ x ∈ S, (S.filter (fun y ↦ y ≠ x ∧ dist x y < r)).card < k) :
    ∃ c : X → Fin k, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c x = c y → r ≤ dist x y := by
  classical
  obtain ⟨c, hc⟩ := finite_relation_coloring
    (fun x y ↦ y ≠ x ∧ dist x y < r)
    (by intro x y h; exact ⟨h.1.symm, by simpa [dist_comm] using h.2⟩)
    (by intro x h; exact h.1 rfl) k hk S hdeg
  refine ⟨c, ?_⟩
  intro x hx y hy hxy he
  by_contra h
  exact hc x hx y hy ⟨hxy.symm, lt_of_not_ge h⟩ he

end OAI.Analysis.Fourier.Restriction
