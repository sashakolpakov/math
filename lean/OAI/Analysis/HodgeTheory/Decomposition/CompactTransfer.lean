import OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! # Compact Transfer -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CompactTransfer.Constructions

noncomputable section

/-! Transfer of total boundedness under a proved comparison of pairwise
distances. This will carry coordinate compactness to genuine manifold L². -/

open Set _root_.Metric

theorem totallyBounded_image_of_dist_le {A X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : A → X) (g : A → Y)
    (S : Set A) (C : ℝ) (hC : 0 < C)
    (h : ∀ a ∈ S, ∀ b ∈ S, dist (g a) (g b) ≤ C * dist (f a) (f b))
    (hf : TotallyBounded (f '' S)) : TotallyBounded (g '' S) := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨T, hTsub, hTfin, hcover⟩ := Metric.finite_approx_of_totallyBounded hf (ε / C) (div_pos hε hC)
  have hlift : ∀ t : T, ∃ a : A, a ∈ S ∧ f a = t.val := fun t => hTsub t.property
  choose lift hliftS hliftF using hlift
  let : Fintype T := hTfin.fintype
  refine ⟨Set.range (fun t : T => g (lift t)), Set.finite_range _, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨t, ht, hclose⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_image_of_mem f ha))
  apply Set.mem_iUnion₂.mpr
  refine ⟨g (lift ⟨t, ht⟩), ⟨⟨t, ht⟩, rfl⟩, ?_⟩
  change dist (g a) (g (lift ⟨t, ht⟩)) < ε
  calc
    _ ≤ C * dist (f a) (f (lift ⟨t, ht⟩)) := h a ha _ (hliftS _)
    _ = C * dist (f a) t := by rw [hliftF]
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hclose hC
    _ = ε := mul_div_cancel₀ ε hC.ne'

end

end OAI.Analysis.HodgeTheory.Decomposition.CompactTransfer.Constructions
