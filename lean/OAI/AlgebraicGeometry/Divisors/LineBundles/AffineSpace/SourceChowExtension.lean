import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceCycleGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourcePrincipalRelations
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Source Chow Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowExtension.BundleCycles

noncomputable section

/-! # LineBundleCycles: genuine Chow pullback for a morphism with fixed-dimensional affine-space source charts -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

theorem affineSpaceSourceGradedCycleExtension_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    SourceCycleGrading.BundleCycles.affineSpaceSourceGradedCycleExtension p f r h d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (p ≫ f) (d + r) (Integral.PulledSupport.BundleCycles.integralPulledSupport p W)
        (Integral.PulledSupport.BundleCycles.integralPulledSupportFunction p W g) := by
  have hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Integral.PulledSupport.BundleCycles.integralPulledSupport p W) (p ≫ f) = (d + r) + 1 := by
    rw [SourceCycleGrading.BundleCycles.affineSpaceSourcePulledSupport_dimension p f r h, hW]
    omega
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (p ≫ f) (d + r)
  rw [SourceCycleGrading.BundleCycles.affineSpaceSourceGradedCycleExtension_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW,
    SourcePrincipalRelations.BundleCycles.affineSpaceSourceCycleExtension_principal p h.forget W g hg,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (p ≫ f) (d + r) (Integral.PulledSupport.BundleCycles.integralPulledSupport p W) hdim]

theorem affineSpaceSourceGradedCycleExtension_isPrincipal (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ)
    (hz : DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ f d z) :
    DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ (p ≫ f) (d + r) (SourceCycleGrading.BundleCycles.affineSpaceSourceGradedCycleExtension p f r h d z) := by
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  refine ⟨Integral.PulledSupport.BundleCycles.integralPulledSupport p W, ?_, Integral.PulledSupport.BundleCycles.integralPulledSupportFunction p W g,
    Integral.PulledSupport.BundleCycles.integralPulledSupportFunction_ne_zero p W g hg,
    affineSpaceSourceGradedCycleExtension_principal p f r h d W hW g hg⟩
  rw [SourceCycleGrading.BundleCycles.affineSpaceSourcePulledSupport_dimension p f r h, hW]
  omega

theorem affineSpaceSourceGradedCycleExtension_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (p ≫ f) (d + r)).comap (SourceCycleGrading.BundleCycles.affineSpaceSourceGradedCycleExtension p f r h d) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact Submodule.subset_span (affineSpaceSourceGradedCycleExtension_isPrincipal p f r h d z hz)

def affineSpaceSourceChowExtension (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) (d + r) :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (p ≫ f) (d + r))
    (SourceCycleGrading.BundleCycles.affineSpaceSourceGradedCycleExtension p f r h d) (affineSpaceSourceGradedCycleExtension_relations p f r h d)

theorem affineSpaceSourceChowExtension_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    affineSpaceSourceChowExtension p f r h d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (p ≫ f) (d + r) (SourceCycleGrading.BundleCycles.affineSpaceSourceGradedCycleExtension p f r h d z) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowExtension.BundleCycles
