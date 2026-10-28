import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups

/-! # Principal Lattice Generators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalLatticeGenerators.TestTransport

noncomputable section

/-! The literal principal lattice subgroup can be tested on generators,
including inverse preservation and the original congruence condition. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups

variable {A V J : Type*} [CommRing A] [AddCommGroup V] [Module A V]
  (L : Submodule A V) (b : J → V) (hb : Submodule.span A (Set.range b) = L)
  (N : ℕ) (g : V ≃ₗ[A] V)

include hb in
theorem principalLattice_iff_generators :
    g ∈ AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup L.toAddSubgroup N ↔
      (∀ j, g (b j) ∈ L) ∧ (∀ j, g.symm (b j) ∈ L) ∧
        ∀ j, ∃ y ∈ L, g (b j) - b j = N • y := by
  change ((∀ x, x ∈ L ↔ g x ∈ L) ∧ ∀ x ∈ L, ∃ y ∈ L, g x - x = N • y) ↔ _
  have hgen (j : J) : b j ∈ L := hb ▸ Submodule.subset_span (Set.mem_range_self j)
  constructor
  · intro hg
    refine ⟨fun j => (hg.1 _).mp (hgen j), ?_, fun j => hg.2 _ (hgen j)⟩
    intro j
    have h := (hg.1 (g.symm (b j))).mpr
    exact h (by simpa only [LinearEquiv.apply_symm_apply] using hgen j)
  · rintro ⟨hforward, hinverse, hcong⟩
    have hf : L ≤ L.comap g.toLinearMap := by
      apply le_trans (le_of_eq hb.symm)
      exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hforward j)
    have hi : L ≤ L.comap g.symm.toLinearMap := by
      apply le_trans (le_of_eq hb.symm)
      exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hinverse j)
    refine ⟨fun x => ⟨fun hx => hf hx, fun hx => ?_⟩, ?_⟩
    · have h := hi hx
      change g.symm (g x) ∈ L at h
      simpa only [LinearEquiv.symm_apply_apply] using h
    · intro x hx
      rw [← hb] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, rfl⟩ := hx
          exact hcong j
      | zero => exact ⟨0, L.zero_mem, by simp⟩
      | add x y _ _ hx hy =>
          obtain ⟨u, hu, he⟩ := hx
          obtain ⟨v, hv, hf⟩ := hy
          refine ⟨u + v, L.add_mem hu hv, ?_⟩
          rw [map_add, smul_add, ← he, ← hf]
          abel
      | smul a x _ hx =>
          obtain ⟨y, hy, he⟩ := hx
          refine ⟨a • y, L.smul_mem a hy, ?_⟩
          rw [map_smul, ← smul_sub, he, smul_comm]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalLatticeGenerators.TestTransport
