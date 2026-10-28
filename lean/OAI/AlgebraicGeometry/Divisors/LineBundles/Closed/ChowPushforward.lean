import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.CyclePushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Chow Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: genuine closed-immersion pushforward on rational Chow groups

The actual finite-cycle map sends every principal-divisor generator to
the divisor of the transported function on its actual closed image.
Consequently it preserves the span of rational-equivalence relations
and induces the displayed quotient map.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

/-- The full principal divisor is preserved in the correct dimension grade. -/
theorem closedDimensionCyclePushforward_principal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (i ≫ f) = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (i ≫ f) d W g) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (SupportImage.BundleCycles.closedImageSupport i W) (PrincipalPushforward.BundleCycles.closedImageRationalFunction i W g) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective f d
  rw [CyclePushforward.BundleCycles.closedDimensionCyclePushforward_forget,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (i ≫ f) d W hW,
    PrincipalPushforward.BundleCycles.closedPushforward_principalPointDivisor,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d (SupportImage.BundleCycles.closedImageSupport i W)
      ((SupportImage.BundleCycles.closedImageSupport_dimension i f W).trans hW)]

/-- A defining rational-equivalence generator maps to a defining generator. -/
theorem closedDimensionCyclePushforward_isPrincipal (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ)
    (hz : DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ (i ≫ f) d z) :
    DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ f d (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d z) := by
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  exact ⟨SupportImage.BundleCycles.closedImageSupport i W, (SupportImage.BundleCycles.closedImageSupport_dimension i f W).trans hW,
    PrincipalPushforward.BundleCycles.closedImageRationalFunction i W g, PrincipalPushforward.BundleCycles.closedImageRationalFunction_ne_zero i W g hg,
    closedDimensionCyclePushforward_principal i f d W hW g⟩

/-- The complete rational-equivalence submodule is preserved. -/
theorem closedDimensionCyclePushforward_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).comap (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact Submodule.subset_span (closedDimensionCyclePushforward_isPrincipal i f d z hz)

/-- Closed pushforward on the genuine dimension-graded Chow quotients. -/
def closedChowPushforward (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d)
    (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d) (closedDimensionCyclePushforward_relations i f d)

@[simp]
theorem closedChowPushforward_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :
    closedChowPushforward i f d (DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ f d (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d z) := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPushforward.BundleCycles
