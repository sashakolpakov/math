import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Chow Point Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowPointClass.Cycles

noncomputable section

/-! # LineBundleCycles: the actual point-cycle formula for affine-space bundle Chow pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r)

theorem affineBundleExtension_dimensionComponent (d : ℕ) (z : X →₀ ℚ) :
    Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (p ≫ f) (d + r) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) =
      CycleGrading.Cycles.affineBundleGradedCycleExtension p f r h d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z) := by
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
        (CycleGrading.Cycles.affineBundleDimensionPointMap p f r h d x') q).trans Finsupp.mapDomain_single.symm
    · have hy : Foundations.Scheme.SupportDimension.supportTranscendenceDimension
          (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x)) (p ≫ f) ≠ d + r := by
        rw [CycleGrading.Cycles.affineBundleFiberGenericPoint_dimension p f r h]
        omega
      rw [Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off (p ≫ f) (d + r) _ _ hy,
        Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off f d _ _ hx, map_zero]

variable [AlgebraicGeometry.IsNoetherian E] [Smooth p]

theorem affineBundleChowExtension_pointClass (d : ℕ) (z : X →₀ ℚ) :
    ChowExtension.Cycles.affineBundleChowExtension p f r h d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + r) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) := by
  change DimensionChow.BundleCycles.dimensionCycleToChowQ (p ≫ f) (d + r)
      (CycleGrading.Cycles.affineBundleGradedCycleExtension p f r h d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z)) =
    DimensionChow.BundleCycles.dimensionCycleToChowQ (p ≫ f) (d + r)
      (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (p ≫ f) (d + r) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z))
  rw [affineBundleExtension_dimensionComponent]

theorem affineBundleChowExtension_independent_charts (h' : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r) (d : ℕ) :
    ChowExtension.Cycles.affineBundleChowExtension p f r h d = ChowExtension.Cycles.affineBundleChowExtension p f r h' d := by
  ext a
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, affineBundleChowExtension_pointClass]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowPointClass.Cycles
