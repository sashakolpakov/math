import Mathlib.Topology.KrullDimension

/-! # Subset Dimension Drop -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.SubsetDimensionDrop

noncomputable section

/-! A strict chain in a proper closed subset of an irreducible space can
be extended by the ambient space. Hence a finite dimension bound drops
by at least one on that closed subset. -/
open _root_.TopologicalSpace _root_.Topology _root_.Order
universe u v

theorem krullDim_lt_of_every_image_extends
    {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]
    (f : α → β) (hf : StrictMono f) (n : ℕ) (hβ : Order.krullDim β ≤ n)
    (he : ∀ a, ∃ b, f a < b) : Order.krullDim α < n := by
  apply Order.krullDim_lt_coe_iff.mpr
  intro p
  obtain ⟨b, hb⟩ := he p.last
  let q : LTSeries β := (p.map f hf).snoc b hb
  have hq := (LTSeries.length_le_krullDim q).trans hβ
  change ((p.length + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) at hq
  have hn : p.length + 1 ≤ n := by exact_mod_cast hq
  exact Nat.lt_of_succ_le hn

theorem properClosed_topologicalKrullDim_lt
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (C : Set X) (hC : IsClosed C) (hproper : C ≠ Set.univ)
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) : topologicalKrullDim C < n := by
  let f := IrreducibleCloseds.map (Subtype.val : C → X) continuous_subtype_val
  let Z : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  apply krullDim_lt_of_every_image_extends f
    (IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal) n hdim
  intro Y
  refine ⟨Z, lt_of_le_not_ge (show f Y ≤ Z from Set.subset_univ _) ?_⟩
  intro hge
  have hsub : (f Y : Set X) ⊆ C :=
    closure_minimal (by rintro _ ⟨y, _, rfl⟩; exact y.property) hC
  apply hproper
  apply Set.eq_univ_iff_forall.mpr
  intro x
  apply hsub
  exact hge (Set.mem_univ x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.SubsetDimensionDrop
