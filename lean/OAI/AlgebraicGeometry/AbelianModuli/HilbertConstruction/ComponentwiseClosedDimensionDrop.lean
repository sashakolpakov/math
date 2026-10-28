import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.SubsetDimensionDrop

/-! # Componentwise Closed Dimension Drop -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComponentwiseClosedDimensionDrop

noncomputable section

/-! A closed cut drops dimension if every irreducible component that it
contains is already a single point. Thus isolated points may remain
while positive-dimensional components are cut properly. -/
open _root_.TopologicalSpace _root_.Topology _root_.Order
universe u v

theorem krullDim_le_of_nonminimal_images_extend
    {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]
    (f : α → β) (hf : StrictMono f) (n : ℕ) (hβ : Order.krullDim β ≤ (n + 1 : ℕ))
    (he : ∀ a, IsMin a ∨ ∃ b, f a < b) : Order.krullDim α ≤ n := by
  have hlt : Order.krullDim α < (n + 1 : ℕ) := by
    apply Order.krullDim_lt_coe_iff.mpr
    intro p
    rcases he p.last with hmin | ⟨b, hb⟩
    · have hh : p.head = p.last := le_antisymm p.head_le_last (hmin p.head_le_last)
      have hz : p.length = 0 := by
        simpa using (congrArg Fin.val (p.strictMono.injective hh)).symm
      rw [hz]
      exact Nat.zero_lt_succ n
    · let q : LTSeries β := (p.map f hf).snoc b hb
      have hq := (LTSeries.length_le_krullDim q).trans hβ
      change ((p.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) at hq
      have hn : p.length + 1 ≤ n + 1 := by exact_mod_cast hq
      exact Nat.lt_succ_of_le (Nat.le_of_succ_le_succ hn)
  simpa only [Nat.cast_add, Nat.cast_one, ENat.WithBot.lt_add_one_iff] using hlt

theorem closedCut_topologicalKrullDim_le
    {X : Type u} [TopologicalSpace X] (C : Set X) (hC : IsClosed C)
    (n : ℕ) (hdim : topologicalKrullDim X ≤ (n + 1 : ℕ))
    (hcomponents : ∀ Z ∈ irreducibleComponents X, Z ⊆ C → Z.Subsingleton) :
    topologicalKrullDim C ≤ n := by
  let f := IrreducibleCloseds.map (Subtype.val : C → X) continuous_subtype_val
  apply krullDim_le_of_nonminimal_images_extend f
    (IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal) n hdim
  intro Y
  obtain ⟨Z, hZ, hYZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (f Y : Set X) (f Y).isIrreducible
  let W : IrreducibleCloseds X := ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents Z hZ⟩
  have hle : f Y ≤ W := hYZ
  by_cases heq : f Y = W
  · left
    have hWC : Z ⊆ C := by
      change (W : Set X) ⊆ C
      rw [← heq]
      exact closure_minimal (by rintro _ ⟨y, _, rfl⟩; exact y.property) hC
    have hs := hcomponents Z hZ hWC
    have hY : (Y : Set C).Subsingleton := by
      intro y hy z hz
      apply Subtype.ext
      exact hs (hYZ (subset_closure (Set.mem_image_of_mem _ hy)))
        (hYZ (subset_closure (Set.mem_image_of_mem _ hz)))
    intro V hVY
    obtain ⟨z, hz⟩ := V.isIrreducible.nonempty
    intro y hy
    exact (hY hy (hVY hz)).symm ▸ hz
  · exact Or.inr ⟨W, lt_of_le_not_ge hle (fun hge => heq (le_antisymm hle hge))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComponentwiseClosedDimensionDrop
