import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CyclePartition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IsoOpenChow

/-! # Clopen Chow Decomposition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ClopenChowDecomposition.BundleCycles

noncomputable section

/-! Chow classes decompose across a finite disjoint cover by actual
open and closed subschemes, so their restrictions jointly detect them. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    {ι : Type} [Fintype ι] (U : ι → Scheme.{0}) [∀ k, AlgebraicGeometry.IsNoetherian (U k)]
    (i : ∀ k, U k ⟶ X) [∀ k, IsOpenImmersion (i k)] [∀ k, IsClosedImmersion (i k)]
    (hcover : ∀ x : X, ∃! k, x ∈ Set.range (i k))

include hcover in
theorem finiteClopenChow_decomposition (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    ∑ k, Closed.ChowPushforward.BundleCycles.closedChowPushforward (i k) f d (Open.ChowRestriction.BundleCycles.openChowRestriction (i k) f d α) = α := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z]
  simp only [Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass]
  rw [← map_sum]
  apply congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ f d)
  exact Point.CyclePartition.BundleCycles.pointCycle_finitePartition (fun k => U k) (fun k => i k)
    (fun k => (i k).isOpenEmbedding.injective) hcover _

include hcover in
theorem finiteClopenChow_joint_zero (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d)
    (hα : ∀ k, Open.ChowRestriction.BundleCycles.openChowRestriction (i k) f d α = 0) : α = 0 := by
  rw [← finiteClopenChow_decomposition f U i hcover d α]
  simp only [hα, map_zero, Finset.sum_const_zero]

include hcover in
theorem finiteClopenChow_joint_injective (d : ℕ) (α β : DimensionChow.BundleCycles.DimensionChowQ f d)
    (hαβ : ∀ k, Open.ChowRestriction.BundleCycles.openChowRestriction (i k) f d α = Open.ChowRestriction.BundleCycles.openChowRestriction (i k) f d β) : α = β := by
  apply sub_eq_zero.mp
  apply finiteClopenChow_joint_zero f U i hcover d (α - β)
  intro k
  rw [map_sub, hαβ k, sub_self]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ClopenChowDecomposition.BundleCycles
