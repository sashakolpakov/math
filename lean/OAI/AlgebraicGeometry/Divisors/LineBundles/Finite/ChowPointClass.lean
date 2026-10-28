import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleChow

/-! # Chow Point Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite Chow pushforward commutes with taking the actual dimension component
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

def schemeDimensionComponent {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) :
    (X →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Finsupp.lcomapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective

theorem schemeDimensionComponent_single {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d) (q : ℚ) :
    schemeDimensionComponent f d (Finsupp.single x.1 q) = Finsupp.single x q :=
  Finsupp.comapDomain_single (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) x q
    (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective.injOn

theorem schemeDimensionComponent_single_off {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (d : ℕ) (x : X) (q : ℚ)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f ≠ d) :
    schemeDimensionComponent f d (Finsupp.single x q) = 0 := by
  apply Finsupp.comapDomain_single_of_not_mem_range
  rintro ⟨y, hy⟩
  exact hx (hy ▸ y.property)

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) [IsFinite i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

theorem finitePushforward_dimensionComponent (d : ℕ) (z : X →₀ ℚ) :
    schemeDimensionComponent f d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i z) =
      CyclePushforward.BundleCycles.finiteDimensionCyclePushforward i f d (schemeDimensionComponent (i ≫ f) d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x q =>
    by_cases hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) = d
    · let x' : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d := ⟨x, hx⟩
      rw [IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, schemeDimensionComponent_single (i ≫ f) d x']
      exact (schemeDimensionComponent_single f d (CyclePushforward.BundleCycles.finiteDimensionPointMap i f d x') _).trans
        (CyclePushforward.BundleCycles.finiteDimensionCyclePushforward_single i f d x' q).symm
    · have hy : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i x)) f ≠ d :=
        fun h => hx ((PointSupport.BundleCycles.pointClosure_dimension_finite i f x).symm.trans h)
      rw [IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, schemeDimensionComponent_single_off f d _ _ hy,
        schemeDimensionComponent_single_off (i ≫ f) d _ _ hx, map_zero]

theorem finiteChowPushforward_pointClass [AlgebraicGeometry.IsNoetherian Y]
    [LocallyOfFiniteType f] (d : ℕ) (z : X →₀ ℚ) :
    ChowPushforward.BundleCycles.finiteChowPushforward i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i z) := by
  change DimensionChow.BundleCycles.dimensionCycleToChowQ f d
      (CyclePushforward.BundleCycles.finiteDimensionCyclePushforward i f d (schemeDimensionComponent (i ≫ f) d z)) =
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d (schemeDimensionComponent f d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i z))
  exact congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ f d) (finitePushforward_dimensionComponent i f d z).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass.BundleCycles
