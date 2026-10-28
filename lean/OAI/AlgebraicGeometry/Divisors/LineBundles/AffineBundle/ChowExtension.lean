import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.CycleGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpacePrincipalRelations
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Chow Extension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowExtension.Cycles

noncomputable section

section

/-! # LineBundleCycles: genuine Chow pullback for a constant-rank affine-space bundle -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r)

theorem affineBundleGradedCycleExtension_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    CycleGrading.Cycles.affineBundleGradedCycleExtension p f r h d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (p ≫ f) (d + r) (Integral.PulledSupport.BundleCycles.integralPulledSupport p W)
        (Integral.PulledSupport.BundleCycles.integralPulledSupportFunction p W g) := by
  have hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Integral.PulledSupport.BundleCycles.integralPulledSupport p W) (p ≫ f) = (d + r) + 1 := by
    rw [CycleGrading.Cycles.integralPulledSupport_dimension p f r h, hW]
    omega
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (p ≫ f) (d + r)
  rw [CycleGrading.Cycles.affineBundleGradedCycleExtension_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW,
    AffineSpacePrincipalRelations.BundleCycles.locallyAffineSpaceCycleExtension_principal p h.forget W g hg,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (p ≫ f) (d + r) (Integral.PulledSupport.BundleCycles.integralPulledSupport p W) hdim]

theorem affineBundleGradedCycleExtension_isPrincipal (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ)
    (hz : DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ f d z) :
    DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ (p ≫ f) (d + r) (CycleGrading.Cycles.affineBundleGradedCycleExtension p f r h d z) := by
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  refine ⟨Integral.PulledSupport.BundleCycles.integralPulledSupport p W, ?_, Integral.PulledSupport.BundleCycles.integralPulledSupportFunction p W g,
    Integral.PulledSupport.BundleCycles.integralPulledSupportFunction_ne_zero p W g hg,
    affineBundleGradedCycleExtension_principal p f r h d W hW g hg⟩
  rw [CycleGrading.Cycles.integralPulledSupport_dimension p f r h, hW]
  omega

theorem affineBundleGradedCycleExtension_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (p ≫ f) (d + r)).comap (CycleGrading.Cycles.affineBundleGradedCycleExtension p f r h d) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact Submodule.subset_span (affineBundleGradedCycleExtension_isPrincipal p f r h d z hz)

def affineBundleChowExtension (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) (d + r) :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (p ≫ f) (d + r))
    (CycleGrading.Cycles.affineBundleGradedCycleExtension p f r h d) (affineBundleGradedCycleExtension_relations p f r h d)

theorem affineBundleChowExtension_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    affineBundleChowExtension p f r h d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (p ≫ f) (d + r) (CycleGrading.Cycles.affineBundleGradedCycleExtension p f r h d z) := rfl

end

/-! # LineBundleCycles: genuine Chow groups and affine-space bundle pullback over the empty scheme -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem dimensionChow_eq_zero_of_isEmpty {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [IsEmpty X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) : a = 0 := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  have hz : z = 0 := by
    ext x
    exact isEmptyElim x.val
  rw [hz, map_zero]

theorem affineBundleChowExtension_surjective_of_isEmpty {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X] [IsEmpty X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r) (d : ℕ) :
    Function.Surjective (affineBundleChowExtension p f r h d) := by
  have : IsEmpty E := ⟨fun e => isEmptyElim (p e)⟩
  intro a
  exact ⟨0, (map_zero _).trans (dimensionChow_eq_zero_of_isEmpty (p ≫ f) (d + r) a).symm⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowExtension.Cycles
