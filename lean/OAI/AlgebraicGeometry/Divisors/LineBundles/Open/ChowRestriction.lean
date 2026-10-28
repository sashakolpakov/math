import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Chow Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: genuine surjective restriction on rational Chow groups

Restriction sends each principal divisor to the actual principal divisor
on its nonempty restricted support, or to zero when the support is
disjoint from the open. It therefore descends to the actual quotients.
Closing the finitely many generic points of a cycle proves surjectivity.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsOpenImmersion i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem openDimensionCycleRestriction_principal (d : ℕ) (W : IrreducibleCloseds Y)
    [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W)] (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (i ≫ f) d (SupportRestriction.BundleCycles.openRestrictedSupport i W)
        (PrincipalRestriction.BundleCycles.openRestrictedRationalFunction i W g) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (i ≫ f) d
  rw [CycleRestriction.BundleCycles.openDimensionCycleRestriction_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW,
    PrincipalRestriction.BundleCycles.openRestriction_principalPointDivisor,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (i ≫ f) d (SupportRestriction.BundleCycles.openRestrictedSupport i W)
      ((SupportRestriction.BundleCycles.openRestrictedSupport_dimension i W f).trans hW)]

theorem openDimensionCycleRestriction_principal_empty (d : ℕ) (W : IrreducibleCloseds Y)
    [IsEmpty (SupportRestriction.BundleCycles.openSupportPullback i W)] (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) = 0 := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (i ≫ f) d
  rw [CycleRestriction.BundleCycles.openDimensionCycleRestriction_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d W hW,
    PrincipalRestriction.BundleCycles.openRestriction_principalPointDivisor_empty, map_zero]

/-- The relation-preservation proof uses the actual nonempty or empty support pullback. -/
theorem openDimensionCycleRestriction_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d).comap (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d) := by
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, g, hg, rfl⟩
  change CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) ∈
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d
  cases isEmpty_or_nonempty (SupportRestriction.BundleCycles.openSupportPullback i W) with
  | inl h =>
    let := h
    rw [openDimensionCycleRestriction_principal_empty i f d W hW g]
    exact Submodule.zero_mem _
  | inr h =>
    let := h
    exact Submodule.subset_span ⟨SupportRestriction.BundleCycles.openRestrictedSupport i W,
      (SupportRestriction.BundleCycles.openRestrictedSupport_dimension i W f).trans hW, PrincipalRestriction.BundleCycles.openRestrictedRationalFunction i W g,
      PrincipalRestriction.BundleCycles.openRestrictedRationalFunction_ne_zero i W g hg,
      openDimensionCycleRestriction_principal i f d W hW g⟩

/-- Restriction to an open subscheme on the genuine dimension-graded Chow groups. -/
def openChowRestriction (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d)
    (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d) (openDimensionCycleRestriction_relations i f d)

@[simp]
theorem openChowRestriction_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    openChowRestriction i f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) d (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d z) := rfl

/-- Every Chow class on the open comes from closing its finitely many cycle supports. -/
theorem openChowRestriction_surjective (d : ℕ) : Function.Surjective (openChowRestriction i f d) := by
  intro a
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (i ≫ f) d a
  refine ⟨DimensionChow.BundleCycles.dimensionCycleToChowQ f d (CycleRestriction.BundleCycles.openDimensionCycleExtension i f d z), ?_⟩
  rw [openChowRestriction_cycle, CycleRestriction.BundleCycles.openDimensionCycleRestriction_extension]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowRestriction.BundleCycles
