import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.CycleGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.AbsoluteClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericClass

/-! # Over Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.OverGrading.Cycles

noncomputable section

/-! Dimension-graded affine-bundle extension using the given complex
structure map of the total space. The coefficients are the actual
integral generic fiber points, without any loss under grading. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [IsIntegral X.left]
    [AlgebraicGeometry.IsNoetherian X.left] [LocallyOfFiniteType X.hom]
    (f : E ⟶ X) [Smooth f.left] [GeometricallyIntegral f.left]
    (r : ℕ) (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank f.left r)

include h in
omit [Smooth (Over.Hom.left f)] in
theorem affineBundleOver_dimension :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom + r := by
  have hd := CycleGrading.Cycles.affineBundleFiberGenericPoint_dimension f.left X.hom r h (genericPoint X.left)
  rw [Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic, LineBundle.GenericClass.Cycles.genericPointSupport_dimension, LineBundle.GenericClass.Cycles.genericPointSupport_dimension,
    f.w] at hd
  exact hd

def affineBundleOverDimensionPoint (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint E.hom (d + r) := ⟨Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint f.left x.val, by
      have hd := CycleGrading.Cycles.affineBundleFiberGenericPoint_dimension f.left X.hom r h x.val
      rw [f.w] at hd
      exact hd.trans (congrArg (fun n => n + r) x.property)⟩

def affineBundleOverGradedExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint E.hom (d + r) →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (affineBundleOverDimensionPoint f r h d)

omit [AlgebraicGeometry.IsIntegral E.left] [AlgebraicGeometry.IsIntegral X.left] [Smooth (Over.Hom.left f)] in
theorem affineBundleOverGradedExtension_forget (d : ℕ) (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion E.hom (d + r) (affineBundleOverGradedExtension f r h d a) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension f.left (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.hom d a) := by
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding E.hom (d + r))
    (Finsupp.mapDomain (affineBundleOverDimensionPoint f r h d) a) =
    Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint f.left) (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding X.hom d) a)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

omit [AlgebraicGeometry.IsIntegral E.left] [AlgebraicGeometry.IsIntegral X.left] [Smooth (Over.Hom.left f)] in
theorem affineBundleOverGradedExtension_single (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) (a : ℚ) :
    affineBundleOverGradedExtension f r h d (Finsupp.single x a) =
      Finsupp.single (affineBundleOverDimensionPoint f r h d x) a := Finsupp.mapDomain_single

include h in
omit [Smooth (Over.Hom.left f)] in
theorem affineBundleOver_complementDegree (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    (d + r) + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom := by
  rw [affineBundleOver_dimension f r h, ← hd]
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.OverGrading.Cycles
