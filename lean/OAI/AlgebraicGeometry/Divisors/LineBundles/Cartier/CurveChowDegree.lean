import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.DegreeOnSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass

/-! # Curve Chow Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.CurveChowDegree.BundleCycles

noncomputable section

/-! For a proper relative curve with affine-line source charts,
a Cartier divisor isomorphic to the base gives degree minus one
after genuine Chow pullback, for every Chow class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated] [X.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (h : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p 1)
    (s : D ⟶ E) [IsClosedImmersion s] [IsIso (s ≫ p)]
    (hs : IdealBundle.Cycles.HasRegularPrincipalImageIdeals s)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem cartierCurveChow_pullback_degree (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) d
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f 1 h d α)) = -α := by
  let T := (Proper.ChowNe.BundleCycles.properChowPushforward p f d).comp
    ((LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) d).comp
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f 1 h d))
  have hOne (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d) :
      T (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x 1)) =
        -DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x 1) := by
    rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d (Finsupp.single x 1)]
    rw [show Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (Finsupp.single x 1) = Finsupp.single x.val 1 from
      Finsupp.mapDomain_single]
    change Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) d
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f 1 h d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single x.val 1)))) = _
    rw [AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass]
    change Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) d
        (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + 1)
          (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) (Finsupp.single x.val 1)))) = _
    rw [Finsupp.mapDomain_single]
    exact DegreeOnSupport.BundleCycles.cartierIsomorphicDivisor_degree_on_support p h s hs f d x.val x.property
  have H : T.comp (DimensionChow.BundleCycles.dimensionCycleToChowQ f d) = -(DimensionChow.BundleCycles.dimensionCycleToChowQ f d) := by
    apply Finsupp.lhom_ext
    intro x a
    change T (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x a)) =
      -DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x a)
    rw [show Finsupp.single x a = a • Finsupp.single x (1 : ℚ) by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, map_smul, hOne, smul_neg]
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  exact LinearMap.congr_fun H z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.CurveChowDegree.BundleCycles
