import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.CycleTrace
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionPointPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Graded Over Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedOverPushforward.BundleCycles

noncomputable section

/-! Finite pushforward in the literal source and target structure-map
gradings, with its complete residue-weighted point-cycle formula. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [AlgebraicGeometry.IsNoetherian X.left]
    (f : X ⟶ Y) [IsFinite f.left]

def finiteOverDimensionPoint (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d :=
  ⟨f.left x.val, by
    have h := PointSupport.BundleCycles.pointClosure_dimension_finite f.left Y.hom x.val
    rw [f.w] at h
    exact h.trans x.property⟩

def finiteOverGradedPushforward (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d →₀ ℚ) :=
  (ChowPointClass.BundleCycles.schemeDimensionComponent Y.hom d).comp
    ((IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f.left).comp (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.hom d))

omit [IsFinite (Over.Hom.left f)] in
theorem finiteOverGradedPushforward_forget (d : ℕ) (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion Y.hom d (finiteOverGradedPushforward f d a) =
      IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f.left (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.hom d a) := by
  have h := DimensionPointPushforward.BundleCycles.dimensionPointPushforward_forget f.left Y.hom d (DimensionChow.BundleCycles.dimensionCycleTransport f.w.symm d a)
  change Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion Y.hom d
    (ChowPointClass.BundleCycles.schemeDimensionComponent Y.hom d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f.left
      (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f.left ≫ Y.hom) d (DimensionChow.BundleCycles.dimensionCycleTransport f.w.symm d a)))) = _ at h
  rw [DimensionChow.BundleCycles.dimensionCycleTransport_forget] at h
  exact h

theorem finiteOverGradedPushforward_single (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) (a : ℚ) :
    finiteOverGradedPushforward f d (Finsupp.single x a) =
      Finsupp.single (finiteOverDimensionPoint f d x) (a * (f.left.residueDegree x.val : ℚ)) := by
  change ChowPointClass.BundleCycles.schemeDimensionComponent Y.hom d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f.left
    (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding X.hom d) (Finsupp.single x a))) = _
  rw [Finsupp.mapDomain_single, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single]
  exact ChowPointClass.BundleCycles.schemeDimensionComponent_single Y.hom d (finiteOverDimensionPoint f d x) _

theorem finiteOverDimensionPoint_support (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    irreducibleSetEquivPoints.symm (finiteOverDimensionPoint f d x).val =
      CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f (irreducibleSetEquivPoints.symm x.val) := by
  apply irreducibleSetEquivPoints.injective
  rw [OrderIso.apply_symm_apply, CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport_genericPoint, OrderIso.apply_symm_apply]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedOverPushforward.BundleCycles
