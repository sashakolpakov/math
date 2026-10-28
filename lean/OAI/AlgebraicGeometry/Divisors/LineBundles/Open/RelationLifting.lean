import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction

/-! # Relation Lifting -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelationLifting.BundleCycles

noncomputable section

/-!
# LineBundleCycles: lifting every rational-equivalence relation from an open

Each principal relation on the open lifts by closing its actual integral
support and extending its function through the generic-stalk isomorphism.
Linear extension lifts the entire relation submodule. A Chow class
vanishing on the open consequently has a cycle representative whose
restriction is exactly zero.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsOpenImmersion i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem openClosure_gradedPrincipal (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (i ≫ f) = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (PrincipalRestriction.BundleCycles.openClosureSupport i W) (PrincipalRestriction.BundleCycles.openClosureRationalFunction i W g)) =
      Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (i ≫ f) d W g := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (i ≫ f) d
  rw [CycleRestriction.BundleCycles.openDimensionCycleRestriction_forget,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d (PrincipalRestriction.BundleCycles.openClosureSupport i W)
      ((PrincipalRestriction.BundleCycles.openClosureSupport_dimension i W f).trans hW),
    PrincipalRestriction.BundleCycles.openClosure_principalPointDivisor, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (i ≫ f) d W hW]

/-- Every relation on the open is the restriction of an actual ambient relation. -/
theorem openDimensionCycleRestriction_relations_lift (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).map (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d) := by
  apply Submodule.span_le.mpr
  rintro z ⟨W, hW, g, hg, rfl⟩
  refine Submodule.mem_map.mpr ⟨Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (PrincipalRestriction.BundleCycles.openClosureSupport i W)
    (PrincipalRestriction.BundleCycles.openClosureRationalFunction i W g), ?_, openClosure_gradedPrincipal i f d W hW g⟩
  exact Submodule.subset_span ⟨PrincipalRestriction.BundleCycles.openClosureSupport i W, (PrincipalRestriction.BundleCycles.openClosureSupport_dimension i W f).trans hW,
    PrincipalRestriction.BundleCycles.openClosureRationalFunction i W g, PrincipalRestriction.BundleCycles.openClosureRationalFunction_ne_zero i W g hg, rfl⟩

theorem openDimensionCycleRestriction_relations_image (d : ℕ) :
    (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).map (CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d) =
      DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d :=
  (Submodule.map_le_iff_le_comap.mpr (ChowRestriction.BundleCycles.openDimensionCycleRestriction_relations i f d)).antisymm
    (openDimensionCycleRestriction_relations_lift i f d)

/-- A class vanishing on the open has a finite cycle representative supported outside it. -/
theorem openChowRestriction_exists_zero_restriction (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d)
    (ha : ChowRestriction.BundleCycles.openChowRestriction i f d a = 0) :
    ∃ z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ,
      DimensionChow.BundleCycles.dimensionCycleToChowQ f d z = a ∧ CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d z = 0 := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  have hz : CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d z ∈ DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (i ≫ f) d :=
    (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff (i ≫ f) d _).mp ha
  obtain ⟨v, hv, hres⟩ := Submodule.mem_map.mp (openDimensionCycleRestriction_relations_lift i f d hz)
  refine ⟨z - v, ?_, ?_⟩
  · rw [map_sub, (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff f d v).mpr hv, sub_zero]
  · rw [map_sub, hres, sub_self]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelationLifting.BundleCycles
