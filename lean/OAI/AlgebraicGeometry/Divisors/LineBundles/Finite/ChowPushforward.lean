import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.CyclePushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Divisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Chow Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite pushforward on genuine dimension-graded rational Chow groups
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] (i : X ⟶ Y) [IsFinite i]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem finiteDimensionCyclePushforward_principal (d : ℕ) (x : X)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField) (hg : g ≠ 0) :
    CyclePushforward.BundleCycles.finiteDimensionCyclePushforward i f d
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (i ≫ f) d (irreducibleSetEquivPoints.symm x) g) =
        Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (irreducibleSetEquivPoints.symm (i x))
          (FiniteSupport.Divisor.BundleCycles.finitePointSupportNorm i x g) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective f d
  rw [CyclePushforward.BundleCycles.finiteDimensionCyclePushforward_forget,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (i ≫ f) d _ hx,
    FiniteSupport.Divisor.BundleCycles.finitePushforward_principalPointSupport i f x g hg,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d _ ((PointSupport.BundleCycles.pointClosure_dimension_finite i f x).trans hx)]

theorem finiteDimensionCyclePushforward_isPrincipal (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ)
    (hz : DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ (i ≫ f) d z) :
    DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ f d (CyclePushforward.BundleCycles.finiteDimensionCyclePushforward i f d z) := by
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  obtain ⟨x, rfl⟩ := irreducibleSetEquivPoints.symm.surjective W
  exact ⟨irreducibleSetEquivPoints.symm (i x), (PointSupport.BundleCycles.pointClosure_dimension_finite i f x).trans hW,
    FiniteSupport.Divisor.BundleCycles.finitePointSupportNorm i x g, FiniteSupport.Divisor.BundleCycles.finitePointSupportNorm_ne_zero i x g hg,
    finiteDimensionCyclePushforward_principal i f d x hW g hg⟩

theorem finiteDimensionCyclePushforward_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).comap (CyclePushforward.BundleCycles.finiteDimensionCyclePushforward i f d) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact Submodule.subset_span (finiteDimensionCyclePushforward_isPrincipal i f d z hz)

def finiteChowPushforward (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d)
    (CyclePushforward.BundleCycles.finiteDimensionCyclePushforward i f d) (finiteDimensionCyclePushforward_relations i f d)

@[simp]
theorem finiteChowPushforward_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :
    finiteChowPushforward i f d (DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ f d (CyclePushforward.BundleCycles.finiteDimensionCyclePushforward i f d z) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPushforward.BundleCycles
