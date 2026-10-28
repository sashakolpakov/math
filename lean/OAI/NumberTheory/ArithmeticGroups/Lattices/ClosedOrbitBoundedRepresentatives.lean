import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Cover
import OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitQuotient

/-! # Closed Orbit Bounded Representatives -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitBoundedRepresentatives.Construction

noncomputable section

section

/-! Bounded subsets of a closed orbit admit representatives in a
compact subset of the acting locally compact group. -/

open Set MulAction

theorem closed_orbit_bounded_compact_representatives
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G]
    [NormedAddCommGroup V] [ProperSpace V] [MulAction G V] [ContinuousSMul G V]
    (v : V) (hv : IsClosed (orbit G v)) (R : ℝ) :
    ∃ C : Set G, IsCompact C ∧
      ∀ g : G, ‖g • v‖ ≤ R → ∃ c ∈ C, c • v = g • v := by
  let O := orbit G v
  let : LocallyCompactSpace O := hv.locallyCompactSpace
  let : ContinuousSMul G O := ⟨by
    apply Continuous.subtype_mk
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)⟩
  let v₀ : O := ⟨v, mem_orbit_self v⟩
  let f : G → O := fun g => g • v₀
  have hopen : IsOpenMap f := isOpenMap_smul_of_sigmaCompact v₀
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := y.property
    exact ⟨g, Subtype.ext hg⟩
  let D : Set O := {y | ‖y.val‖ ≤ R}
  have hD : IsCompact D := by
    have he : D = (Subtype.val : O → V) ⁻¹' Metric.closedBall 0 R := by
      ext y
      simp only [D, mem_ofPred_eq, mem_preimage, Metric.mem_closedBall, dist_zero_right]
    rw [he]
    exact hv.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage (isCompact_closedBall 0 R)
  obtain ⟨C, hC, hcover⟩ := Compact.Cover.Construction.exists_compact_cover_of_compact_open_image f hopen hsurj D hD
  refine ⟨C, hC, fun g hg => ?_⟩
  have hfg : f g ∈ D := hg
  obtain ⟨c, hc, he⟩ := hcover hfg
  exact ⟨c, hc, congrArg Subtype.val he⟩

end

/-! An automorphism preserving a stabilizer induces a well-defined
map of its orbit, and takes bounded closed-orbit portions to bounded portions. -/

open Set MulAction

theorem stabilizer_preserving_map_orbit_eq
    {G V : Type*} [Group G] [MulAction G V]
    (θ : G →* G) (v : V) (hθ : ∀ h : G, h • v = v → θ h • v = v)
    (g h : G) (he : g • v = h • v) : θ g • v = θ h • v := by
  have hs : (g⁻¹ * h) • v = v := by
    rw [mul_smul, ← he, inv_smul_smul]
  have ht := congrArg (fun w => θ g • w) (hθ (g⁻¹ * h) hs)
  simpa only [map_mul, map_inv, mul_smul, smul_inv_smul] using ht.symm

theorem closed_orbit_stabilizer_preserving_map_bound
    {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G]
    [NormedAddCommGroup V] [ProperSpace V] [MulAction G V] [ContinuousSMul G V]
    (θ : G →* G) (hθc : Continuous θ) (v : V) (hv : IsClosed (orbit G v))
    (hθ : ∀ h : G, h • v = v → θ h • v = v) (R : ℝ) :
    ∃ T : ℝ, ∀ g : G, ‖g • v‖ ≤ R → ‖θ g • v‖ ≤ T := by
  obtain ⟨C, hC, hrep⟩ := closed_orbit_bounded_compact_representatives v hv R
  have hc : Continuous (fun g : G => ‖θ g • v‖) := continuous_norm.comp (hθc.smul continuous_const)
  obtain ⟨T, hT⟩ := hC.bddAbove_image hc.continuousOn
  refine ⟨T, fun g hg => ?_⟩
  obtain ⟨c, hc, he⟩ := hrep g hg
  rw [← stabilizer_preserving_map_orbit_eq θ v hθ c g he]
  exact hT ⟨c, hc, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitBoundedRepresentatives.Construction
