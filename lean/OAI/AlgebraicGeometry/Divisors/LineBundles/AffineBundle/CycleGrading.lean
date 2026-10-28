import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.BundleRankZero
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Cycle Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.CycleGrading.Cycles

noncomputable section

section

/-! # LineBundleCycles: genuine dimension shift from actual constant-rank affine-space bundle charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : LineBundles.AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r)

include h

theorem affineBundleFiberGenericPoint_dimension (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x)) (p ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + r := by
  obtain ⟨U, i, ι, hι, j, hi, hj, hx, hs, hr⟩ := h x
  let := hι
  let := hi
  let := hj
  have : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian i
  obtain ⟨u, rfl⟩ := hx
  rw [← Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_naturality p (AffineSpace ι U ↘ U) i j hs u,
    ImmersionDimension.BundleCycles.pointClosure_dimension_immersion j]
  have he : j ≫ (p ≫ f) = (AffineSpace ι U ↘ U) ≫ (i ≫ f) := by
    rw [← Category.assoc, ← hs.w, Category.assoc]
  rw [he, LineBundles.AffineSpace.CycleGrading.BundleCycles.affineSpaceFiberGenericPoint_dimension, hr, ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i]

theorem integralPulledSupport_dimension [Smooth p] (W : IrreducibleCloseds X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Integral.PulledSupport.BundleCycles.integralPulledSupport p W) (p ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f + r := by
  rw [Integral.PulledSupport.BundleCycles.integralPulledSupport_eq_pointClosure, affineBundleFiberGenericPoint_dimension p f r h,
    irreducibleSetEquivPoints.symm_apply_apply]

end

/-! # LineBundleCycles: the actual dimension-graded cycle pullback of a constant-rank affine-space bundle -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : LineBundles.AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r)

def affineBundleDimensionPointMap (d : ℕ) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d → Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) (d + r) :=
  fun x => ⟨Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x.1,
    (affineBundleFiberGenericPoint_dimension p f r h x.1).trans
      (congrArg (fun n => n + r) x.2)⟩

def affineBundleGradedCycleExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) (d + r) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (affineBundleDimensionPointMap p f r h d)

theorem affineBundleGradedCycleExtension_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) (d + r) (affineBundleGradedCycleExtension p f r h d z) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) := by
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding (p ≫ f) (d + r))
      (Finsupp.mapDomain (affineBundleDimensionPointMap p f r h d) z) =
    Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.CycleGrading.Cycles
