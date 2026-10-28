import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.PointPreimage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CyclePartition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.PullbackRange

/-! # Clopen Point Preimage -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ClopenPointPreimage.Cycles

noncomputable section

/-! Point-cycle preimages glue across a finite disjoint cover by actual
open and closed base changes, allowing the relative ranks to vary. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineBundlePointChow_preimage_of_clopen {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    {ι : Type} [Fintype ι] (U V : ι → Scheme.{0})
    [∀ k, AlgebraicGeometry.IsNoetherian (U k)] [∀ k, AlgebraicGeometry.IsNoetherian (V k)]
    (q : ∀ k, V k ⟶ U k) [∀ k, Smooth (q k)] [∀ k, GeometricallyIntegral (q k)]
    (i : ∀ k, U k ⟶ X) (j : ∀ k, V k ⟶ E)
    [∀ k, IsOpenImmersion (i k)] [∀ k, IsClosedImmersion (i k)]
    [∀ k, IsOpenImmersion (j k)] [∀ k, IsClosedImmersion (j k)]
    (hs : ∀ k, IsPullback (q k) (j k) (i k) p)
    (r : ι → ℕ) (h : ∀ k, AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank (q k) (r k))
    (hcover : ∀ x : X, ∃! k, x ∈ Set.range (i k)) (β : E →₀ ℚ) :
    ∃ z : X →₀ ℚ, ∀ d : ℕ,
      Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) = Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d β := by
  classical
  let b (k : ι) : V k →₀ ℚ := Finsupp.comapDomain (j k) β (j k).isOpenEmbedding.injective.injOn
  have H : ∀ k, ∃ z : U k →₀ ℚ, ∀ d : ℕ,
      Point.CycleChow.BundleCycles.pointCycleToChowQ (q k ≫ (i k ≫ f)) d (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (q k) z) =
        Point.CycleChow.BundleCycles.pointCycleToChowQ (q k ≫ (i k ≫ f)) d (b k) :=
    fun k => PointPreimage.Cycles.affineBundlePointChow_preimage_of_rank (q k) (i k ≫ f) (r k) (h k) (b k)
  choose z hz using H
  have hc : ∀ x : E, ∃! k, x ∈ Set.range (j k) := by
    intro x
    simpa only [PullbackRange.BundleCycles.range_of_isPullback (hs _).flip, Set.mem_preimage] using hcover (p x)
  refine ⟨∑ k, Finsupp.mapDomain (i k) (z k), ?_⟩
  intro d
  rw [map_sum, map_sum]
  calc
    _ = ∑ k, Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d (Finsupp.mapDomain (j k) (b k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_naturality p (q k) (i k) (j k) (hs k)]
      have he : j k ≫ (p ≫ f) = q k ≫ (i k ≫ f) := by
        rw [← Category.assoc, ← (hs k).w, Category.assoc]
      rw [← Closed.ChowPointClass.BundleCycles.closedChowPushforwardOver_pointClass (j k) (p ≫ f) (q k ≫ (i k ≫ f)) he d,
        hz k d, Closed.ChowPointClass.BundleCycles.closedChowPushforwardOver_pointClass]
    _ = Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d β := by
      rw [← map_sum]
      exact congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d)
        (Point.CyclePartition.BundleCycles.pointCycle_finitePartition (fun k => V k) (fun k => j k)
          (fun k => (j k).isOpenEmbedding.injective) hc β)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ClopenPointPreimage.Cycles
