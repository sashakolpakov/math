import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Source Chow Point Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual point-cycle formula for Chow pullback from affine-space source charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

theorem affineSpaceSourceExtension_dimensionComponent (d : ℕ) (z : X →₀ ℚ) :
    Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (p ≫ f) (d + r) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) =
      SourceCycleGrading.BundleCycles.affineSpaceSourceGradedCycleExtension p f r h d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x q =>
    change Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (p ≫ f) (d + r)
      (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) (Finsupp.single x q)) = _
    rw [Finsupp.mapDomain_single]
    by_cases hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d
    · let x' : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d := ⟨x, hx⟩
      rw [Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single f d x']
      exact (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single (p ≫ f) (d + r)
        (SourceCycleGrading.BundleCycles.affineSpaceSourceDimensionPointMap p f r h d x') q).trans Finsupp.mapDomain_single.symm
    · have hy : Foundations.Scheme.SupportDimension.supportTranscendenceDimension
          (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x)) (p ≫ f) ≠ d + r := by
        rw [SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension p f r h]
        omega
      rw [Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off (p ≫ f) (d + r) _ _ hy,
        Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off f d _ _ hx, map_zero]

variable [AlgebraicGeometry.IsNoetherian E] [Smooth p]

theorem affineSpaceSourceChowExtension_pointClass (d : ℕ) (z : X →₀ ℚ) :
    SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r h d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + r) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) := by
  change DimensionChow.BundleCycles.dimensionCycleToChowQ (p ≫ f) (d + r)
      (SourceCycleGrading.BundleCycles.affineSpaceSourceGradedCycleExtension p f r h d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z)) =
    DimensionChow.BundleCycles.dimensionCycleToChowQ (p ≫ f) (d + r)
      (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (p ≫ f) (d + r) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z))
  rw [affineSpaceSourceExtension_dimensionComponent]

theorem affineSpaceSourceChowExtension_independent_charts (h' : SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (d : ℕ) :
    SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r h d = SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r h' d := by
  ext a
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, affineSpaceSourceChowExtension_pointClass]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass.BundleCycles
