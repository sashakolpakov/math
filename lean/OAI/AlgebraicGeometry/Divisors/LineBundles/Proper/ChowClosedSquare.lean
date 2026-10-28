import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowFunctoriality
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBaseChange

/-! # Chow Closed Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowClosedSquare.BundleCycles

noncomputable section

/-! Proper pushforward through a commuting square agrees with
closed pushforward of the corresponding proper image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U] [E.IsSeparated] [X.IsSeparated] [E'.IsSeparated] [U.IsSeparated]
    (p : E ⟶ X) (q : E' ⟶ U) [IsProper p] [IsProper q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsClosedImmersion i] [IsClosedImmersion j]
    (hs : IsPullback q j i p) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem properChowPushforward_closedSquare (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (q ≫ (i ≫ f)) d) :
    ChowNe.BundleCycles.properChowPushforward p f d
      (Closed.ChowOver.BundleCycles.closedChowPushforwardOver j (q ≫ (i ≫ f)) (p ≫ f)
        (AffineBundle.ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p q i j hs f) d α) =
      Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d (ChowNe.BundleCycles.properChowPushforward q (i ≫ f) d α) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (q ≫ (i ≫ f)) d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion (q ≫ (i ≫ f)) d z, Closed.ChowPointClass.BundleCycles.closedChowPushforwardOver_pointClass,
    ChowNe.BundleCycles.properChowPushforward_pointClass, ChowNe.BundleCycles.properChowPushforward_pointClass, Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass,
    ← IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion j, ← IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion i,
    ← LinearMap.comp_apply (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward p) (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward j), ← IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp,
    ← LinearMap.comp_apply (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i) (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward q), ← IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, hs.w]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowClosedSquare.BundleCycles
