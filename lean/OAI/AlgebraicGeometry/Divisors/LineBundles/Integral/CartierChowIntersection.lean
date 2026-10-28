import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericClass

/-! # Cartier Chow Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierChowIntersection.BundleCycles

noncomputable section

/-! Intersecting the fundamental class with the actual ideal of
an integral effective Cartier divisor gives minus its closed pushforward. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] [AlgebraicGeometry.IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals i)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem integralCartierIdeal_chowClass (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    (Cartier.IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionChowClass f d =
      -Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single (i (genericPoint Z)) 1) := by
  rw [← Cartier.IdealDivisor.BundleCycles.cartierIdealInversePointCycle_class i hi f d hd, CartierDivisor.BundleCycles.integralCartierIdeal_pointCycle,
    Finsupp.single_neg, map_neg]

theorem integralCartierIdeal_chowIntersection [X.IsSeparated] [AlgebraicGeometry.IsNoetherian Z]
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (Cartier.IdealBundle.Cycles.cartierIdealLineBundle i hi) f d
      (Point.CycleChow.BundleCycles.pointCycleToChowQ f (d + 1) (Finsupp.single (genericPoint X) 1)) =
        -Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d
          (Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d (Finsupp.single (genericPoint Z) 1)) := by
  rw [LineBundle.GenericClass.Cycles.separatedLineBundleChowIntersection_generic X _ f d hd,
    integralCartierIdeal_chowClass i hi f d hd, Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass, Finsupp.mapDomain_single]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierChowIntersection.BundleCycles
