import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.CycleGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PrincipalRelations
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Chow Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowExtension.BundleCycles

noncomputable section

/-! # LineBundleCycles: genuine Chow pullback from the original scheme to its relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineGradedCycleExtension_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (Support.BundleCycles.affineLineExtendedSupport X W) (Support.BundleCycles.affineLineExtendedFunction X W g) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
  rw [CycleGrading.BundleCycles.affineLineGradedCycleExtension_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW,
    PrincipalRelations.BundleCycles.affineLineCycleExtension_principal X W g hg,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
      (Support.BundleCycles.affineLineExtendedSupport X W) ((CycleGrading.BundleCycles.affineLineExtendedSupport_dimension X f W).trans
        (congrArg (fun n => n + 1) hW))]

theorem affineLineGradedCycleExtension_isPrincipal (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ)
    (hz : DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ f d z) :
    DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
      (CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d z) := by
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  exact ⟨Support.BundleCycles.affineLineExtendedSupport X W,
    (CycleGrading.BundleCycles.affineLineExtendedSupport_dimension X f W).trans (congrArg (fun n => n + 1) hW),
    Support.BundleCycles.affineLineExtendedFunction X W g, Support.BundleCycles.affineLineExtendedFunction_ne_zero X W g hg,
    affineLineGradedCycleExtension_principal X f d W hW g hg⟩

theorem affineLineGradedCycleExtension_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)).comap
        (CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact Submodule.subset_span (affineLineGradedCycleExtension_isPrincipal X f d z hz)

def affineLineChowExtension (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).mapQ
    (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1))
    (CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d) (affineLineGradedCycleExtension_relations X f d)

@[simp]
theorem affineLineChowExtension_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    affineLineChowExtension X f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d z) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowExtension.BundleCycles
