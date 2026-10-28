import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceRank
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Source Cycle Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceCycleGrading.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual dimension-graded cycle pullback of a morphism with fixed-dimensional affine-space source charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

include h in
theorem affineSpaceSourcePulledSupport_dimension [Smooth p] (W : TopologicalSpace.IrreducibleCloseds X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Integral.PulledSupport.BundleCycles.integralPulledSupport p W) (p ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + r := by
  rw [Integral.PulledSupport.BundleCycles.integralPulledSupport_eq_pointClosure, SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension p f r h,
    irreducibleSetEquivPoints.symm_apply_apply]

def affineSpaceSourceDimensionPointMap (d : ℕ) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d → Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) (d + r) :=
  fun x => ⟨Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x.1,
    (SourceRank.BundleCycles.affineSpaceSourceFiberGenericPoint_dimension p f r h x.1).trans
      (congrArg (fun n => n + r) x.2)⟩

def affineSpaceSourceGradedCycleExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) (d + r) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (affineSpaceSourceDimensionPointMap p f r h d)

theorem affineSpaceSourceGradedCycleExtension_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) (d + r) (affineSpaceSourceGradedCycleExtension p f r h d z) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) := by
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding (p ≫ f) (d + r))
      (Finsupp.mapDomain (affineSpaceSourceDimensionPointMap p f r h d) z) =
    Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceCycleGrading.BundleCycles
