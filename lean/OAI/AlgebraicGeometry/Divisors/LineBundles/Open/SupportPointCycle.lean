import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction

/-! # Support Point Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportPointCycle.BundleCycles

noncomputable section

/-! # LineBundleCycles: open restriction of the full finite cycle pushed from a closed integral support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] (W : IrreducibleCloseds Y)

theorem openRestrictedSupport_pointCycle [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme W →₀ ℚ) :
    Finsupp.comapDomain i (Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) z) i.isOpenEmbedding.injective.injOn =
      Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W))
        (Finsupp.comapDomain (SupportRestriction.BundleCycles.openRestrictedSupportMap i W) z
          (SupportRestriction.BundleCycles.openRestrictedSupportMap i W).isOpenEmbedding.injective.injOn) := by
  ext x
  by_cases hx : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W))
  · obtain ⟨y, rfl⟩ := hx
    have hp : CycleClass.Geometric.GenericPoint.reducedSupportι W (SupportRestriction.BundleCycles.openRestrictedSupportMap i W y) =
        i (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W) y) :=
      congrArg (fun j => j y) (SupportRestriction.BundleCycles.openRestrictedSupportMap_inclusion i W)
    change Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) z (i (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W) y)) = _
    rw [← hp, Finsupp.mapDomain_apply_of_injective (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective,
      Finsupp.mapDomain_apply_of_injective (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W)).isClosedEmbedding.injective]
    rfl
  · have hi : i x ∉ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
      rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
      intro h
      apply hx
      rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι, SupportRestriction.BundleCycles.openRestrictedSupport_coe]
      exact h
    exact (Finsupp.mapDomain_of_notMem_range _ _ hi).trans
      (Finsupp.mapDomain_of_notMem_range _ _ hx).symm

theorem openRestrictedSupport_pointCycle_empty [IsEmpty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme W →₀ ℚ) :
    Finsupp.comapDomain i (Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) z) i.isOpenEmbedding.injective.injOn = 0 := by
  ext x
  apply Finsupp.mapDomain_of_notMem_range
  rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  intro hx
  exact isEmptyElim (Classical.choice ((SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff i W).mpr ⟨x, hx⟩))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportPointCycle.BundleCycles
