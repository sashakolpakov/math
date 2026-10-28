import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Fin

/-! # Generated Twist -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GeneratedTwist

noncomputable section

/-! Actual globally generated sections pad smaller twists to one common original twist exponent. -/

open Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]

theorem holomorphicSection_twist_nonzero_mono (u v : Connecting.holomorphicUnitCohomology E M)
    (hv : HolomorphicSection.Fin.holomorphicLineGloballyGenerated v) (x : M) (n m : ℕ) (hnm : n ≤ m)
    (s : HolomorphicSection.Data.HolomorphicLineSection (u + n • v) ⊤) (hs : HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt (u + n • v) s x) :
    ∃ t : HolomorphicSection.Data.HolomorphicLineSection (u + m • v) ⊤, HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt (u + m • v) t x := by
  by_cases he : n = m
  · subst m
    exact ⟨s, hs⟩
  · have hk : 0 < m - n := Nat.sub_pos_of_lt (lt_of_le_of_ne hnm he)
    obtain ⟨a, ha⟩ := hv x
    obtain ⟨b, hb⟩ := HolomorphicSection.Fin.exists_holomorphicSection_power_nonzero v a x ha (m - n) hk
    have hcast : (u + n • v) + (m - n) • v = u + m • v := by
      rw [add_assoc, ← add_nsmul, Nat.add_sub_of_le hnm]
    exact ⟨HolomorphicSection.Fin.holomorphicSectionCast hcast (TensorSection.holomorphicTensorSection (u + n • v) ((m - n) • v) s b),
      HolomorphicSection.Fin.holomorphicSectionCast_nonzero hcast _ x (TensorSection.holomorphicTensorSection_nonzero _ _ s b x hs hb)⟩

theorem exists_holomorphic_globally_generated_twist [CompactSpace M]
    (u v : Connecting.holomorphicUnitCohomology E M) (hv : HolomorphicSection.Fin.holomorphicLineGloballyGenerated v)
    (hu : ∀ x : M, ∃ n : ℕ, ∃ s : HolomorphicSection.Data.HolomorphicLineSection (u + n • v) ⊤,
      HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt (u + n • v) s x) :
    ∃ N : ℕ, 0 < N ∧ HolomorphicSection.Fin.holomorphicLineGloballyGenerated (u + N • v) := by
  classical
  choose n s hs using hu
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun y : M => {x | HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt (u + n y • v) (s y) x})
    (fun y => HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt_isOpen (u + n y • v) (s y))
    (fun x _ => mem_iUnion.mpr ⟨x, hs x⟩)
  let N := (∑ y ∈ F, n y) + 1
  refine ⟨N, Nat.succ_pos _, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ F, HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt (u + n y • v) (s y) x := by
    simpa only [mem_iUnion, exists_prop, mem_ofPred_eq] using! hF (mem_univ x)
  have hle : n y ≤ N := (Finset.single_le_sum (fun z _ => Nat.zero_le (n z)) hy).trans (Nat.le_succ _)
  exact holomorphicSection_twist_nonzero_mono u v hv x (n y) N hle (s y) hxy

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GeneratedTwist
