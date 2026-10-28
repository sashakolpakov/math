import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrincipalCycleClassZero
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.GradedCycleClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Chow Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowClass.Cycles

noncomputable section

/-! The constructed nonprojective Chow cycle class commutes with the
actual affine-bundle Chow extension in the literal structure-map grading. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [IsIntegral X.left]
    [AlgebraicGeometry.IsNoetherian E.left] [AlgebraicGeometry.IsNoetherian X.left]
    [LocallyOfFiniteType X.hom] (f : E ⟶ X) [Smooth f.left] [GeometricallyIntegral f.left]
    (r : ℕ) (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank f.left r)

omit [AlgebraicGeometry.IsIntegral E.left] [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsNoetherian E.left] [Smooth (Over.Hom.left f)] in
theorem affineBundleOverGradedExtension_transport (d : ℕ) (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    DimensionChow.BundleCycles.dimensionCycleTransport f.w (d + r) (CycleGrading.Cycles.affineBundleGradedCycleExtension f.left X.hom r h d a) =
      OverGrading.Cycles.affineBundleOverGradedExtension f r h d a := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective E.hom (d + r)
  rw [DimensionChow.BundleCycles.dimensionCycleTransport_forget, CycleGrading.Cycles.affineBundleGradedCycleExtension_forget, OverGrading.Cycles.affineBundleOverGradedExtension_forget]

def affineBundleOverChowExtension (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ X.hom d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ E.hom (d + r) :=
  (DimensionChow.BundleCycles.dimensionChowTransport f.w (d + r)).comp (ChowExtension.Cycles.affineBundleChowExtension f.left X.hom r h d)

omit [AlgebraicGeometry.IsIntegral E.left] [AlgebraicGeometry.IsIntegral X.left] in
theorem affineBundleOverChowExtension_cycle (d : ℕ) (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    affineBundleOverChowExtension f r h d (DimensionChow.BundleCycles.dimensionCycleToChowQ X.hom d a) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ E.hom (d + r) (OverGrading.Cycles.affineBundleOverGradedExtension f r h d a) := by
  change DimensionChow.BundleCycles.dimensionChowTransport f.w (d + r)
    (ChowExtension.Cycles.affineBundleChowExtension f.left X.hom r h d (DimensionChow.BundleCycles.dimensionCycleToChowQ X.hom d a)) = _
  rw [ChowExtension.Cycles.affineBundleChowExtension_cycle, DimensionChow.BundleCycles.dimensionChowTransport_cycle, affineBundleOverGradedExtension_transport]

variable [Smooth X.hom] [IsSeparated X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [Smooth E.hom] [IsSeparated E.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]

theorem schemeDimensionChowCycleClass_affineBundle (d p : ℕ)
    (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) (a : DimensionChow.BundleCycles.DimensionChowQ X.hom d) :
    Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass E (d + r) p (OverGrading.Cycles.affineBundleOver_complementDegree f r h d p hd)
      (affineBundleOverChowExtension f r h d a) =
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass X d p hd a) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective X.hom d a
  rw [affineBundleOverChowExtension_cycle, Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass_cycle, Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass_cycle]
  exact LinearMap.congr_fun (GradedCycleClass.Cycles.schemeGradedCycleClass_affineBundle f r h d p hd) z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowClass.Cycles
