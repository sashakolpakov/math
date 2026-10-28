import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRankOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ClopenChowDecomposition

/-! # Rank Chow Detection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.RankChowDetection.Cycles

noncomputable section

/-! Restriction to the finite collection of actual rank strata
jointly detects every dimension-graded Chow class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [GeometricallyIntegral p] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (h : Affine.SpaceChartBaseChange.BundleCycles.HasAffineSpaceCharts p)

theorem affineBundleRankChow_joint_zero (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d)
    (hα : ∀ r : ℕ, Open.ChowRestriction.BundleCycles.openChowRestriction (FiberRankOpen.Cycles.affineBundleRankOpen p f h r).ι f d α = 0) : α = 0 := by
  classical
  let ι := Set.range (FiberRank.Cycles.affineBundleFiberRank p f)
  let : Fintype ι := (FiberRank.Cycles.affineBundleFiberRank_finite p f h).fintype
  let U (r : ι) : Scheme := (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).toScheme
  let i (r : ι) : U r ⟶ X := (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).ι
  let : ∀ r, AlgebraicGeometry.IsNoetherian (U r) := fun r => inferInstanceAs
    (AlgebraicGeometry.IsNoetherian (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).toScheme)
  let : ∀ r, IsOpenImmersion (i r) := fun r => inferInstanceAs
    (IsOpenImmersion (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).ι)
  let : ∀ r, IsClosedImmersion (i r) := fun r => inferInstanceAs
    (IsClosedImmersion (FiberRankOpen.Cycles.affineBundleRankOpen p f h r.val).ι)
  have hc : ∀ x : X, ∃! r : ι, x ∈ Set.range (i r) := by
    intro x
    refine ⟨⟨FiberRank.Cycles.affineBundleFiberRank p f x, ⟨x, rfl⟩⟩, ?_, ?_⟩
    · exact ⟨⟨x, rfl⟩, rfl⟩
    · rintro r ⟨u, rfl⟩
      apply Subtype.ext
      exact u.property.symm
  exact Finite.ClopenChowDecomposition.BundleCycles.finiteClopenChow_joint_zero f U i hc d α (fun r => hα r.val)

theorem affineBundleRankChow_joint_injective (d : ℕ) (α β : DimensionChow.BundleCycles.DimensionChowQ f d)
    (hαβ : ∀ r : ℕ, Open.ChowRestriction.BundleCycles.openChowRestriction (FiberRankOpen.Cycles.affineBundleRankOpen p f h r).ι f d α =
      Open.ChowRestriction.BundleCycles.openChowRestriction (FiberRankOpen.Cycles.affineBundleRankOpen p f h r).ι f d β) : α = β := by
  apply sub_eq_zero.mp
  apply affineBundleRankChow_joint_zero p f h d (α - β)
  intro r
  rw [map_sub, hαβ r, sub_self]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.RankChowDetection.Cycles
