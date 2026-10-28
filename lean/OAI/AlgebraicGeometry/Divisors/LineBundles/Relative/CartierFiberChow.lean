import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass

/-! # Cartier Fiber Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberChow.BundleCycles

noncomputable section

/-! Actual Chow extension commutes with intersection by a
relative Cartier divisor, with the sign of its ideal line bundle. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian D] [E.IsSeparated]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [Smooth (s ≫ p)] [GeometricallyIntegral (s ≫ p)]
    (hs : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals s)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (s ≫ p) r)

theorem relativeCartierIdeal_fiber_chow (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) (d + r)
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d α) =
      -Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm (d + r)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (s ≫ p) f r hq d α) := by
  let T := (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) (d + r)).comp
    (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d)
  let S := -(Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm (d + r)).comp
    (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (s ≫ p) f r hq d)
  have hOne (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d) :
      T (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x 1)) = S (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x 1)) := by
    rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d (Finsupp.single x 1)]
    rw [show Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (Finsupp.single x 1) = Finsupp.single x.val 1 from Finsupp.mapDomain_single]
    change LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) (d + r)
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single x.val 1))) =
      -Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm (d + r)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (s ≫ p) f r hq d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single x.val 1)))
    rw [AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass, AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass,
      Closed.ChowPointClass.BundleCycles.closedChowPushforwardOver_pointClass]
    change LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) (d + r)
      (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) ((d + r) + 1)
        (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) (Finsupp.single x.val 1))) =
      -Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + r)
        (Finsupp.mapDomain s (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (s ≫ p)) (Finsupp.single x.val 1)))
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    exact CartierFiberPoint.BundleCycles.relativeCartierIdeal_fiber_point p s hs f r hp d x.val x.property
  have H : T.comp (DimensionChow.BundleCycles.dimensionCycleToChowQ f d) = S.comp (DimensionChow.BundleCycles.dimensionCycleToChowQ f d) := by
    apply Finsupp.lhom_ext
    intro x a
    change T (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x a)) = S (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x a))
    rw [show Finsupp.single x a = a • Finsupp.single x (1 : ℚ) by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, map_smul, map_smul, hOne]
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  exact LinearMap.congr_fun H z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberChow.BundleCycles
