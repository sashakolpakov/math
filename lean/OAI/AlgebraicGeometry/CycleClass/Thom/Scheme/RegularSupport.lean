import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation

/-! # Regular Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport

noncomputable section

/-! Actual reduced supports and their regular-locus closed analytic embeddings
inside general smooth complex schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] (Z : IrreducibleCloseds X.left)

abbrev supportOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (Geometric.SupportFiniteType.supportStructureMap Z X.hom)

def supportToAmbient : supportOver X Z ⟶ X := Over.homMk (Geometric.GenericPoint.reducedSupportι Z) rfl

instance supportToAmbient_closed : IsClosedImmersion (supportToAmbient X Z).left :=
  inferInstanceAs (IsClosedImmersion (Geometric.GenericPoint.reducedSupportι Z))

abbrev regularOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap Z X.hom))

instance regularOver_integral : IsIntegral (regularOver X Z).left :=
  inferInstanceAs (IsIntegral (Geometric.SmoothStratum.smoothStratum (Geometric.SupportFiniteType.supportStructureMap Z X.hom)))

instance regularOver_smooth : Smooth (regularOver X Z).hom :=
  inferInstanceAs (Smooth (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap Z X.hom)))

def regularToAmbient : regularOver X Z ⟶ X :=
  Over.homMk (Geometric.SmoothStratum.reducedSupportSmoothStratumι Z (Geometric.SupportFiniteType.supportStructureMap Z X.hom))
    (Category.assoc _ _ _)

instance regularToAmbient_immersion : IsImmersion (regularToAmbient X Z).left :=
  inferInstanceAs (IsImmersion (Geometric.SmoothStratum.reducedSupportSmoothStratumι Z (Geometric.SupportFiniteType.supportStructureMap Z X.hom)))

abbrev supportInclusion := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (supportToAmbient X Z)
abbrev regularInclusion := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularToAmbient X Z)
abbrev regularModel := Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension (regularOver X Z).hom) → ℂ

omit [LocallyOfFiniteType X.hom] in
/-- The full support is exactly the inverse image of the original reduced closed set. -/
theorem supportInclusion_range :
    Set.range (supportInclusion X Z) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (Z : Set X.left) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion (supportToAmbient X Z)]
  exact congrArg (fun S : Set X.left => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S)
    (Geometric.GenericPoint.range_reducedSupportι Z)

theorem regularInclusion_range :
    Set.range (regularInclusion X Z) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹'
      Set.range (Geometric.SmoothStratum.reducedSupportSmoothStratumι Z (Geometric.SupportFiniteType.supportStructureMap Z X.hom)) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion (regularToAmbient X Z)

/-- The actual analytic points over the algebraic singular boundary. -/
def analyticBoundary : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' Geometric.StratumDimension.supportSingularBoundary Z X.hom

theorem analyticBoundary_closed : IsClosed (analyticBoundary X Z) :=
  (Geometric.StratumDimension.isClosed_supportSingularBoundary Z X.hom).preimage ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_underlying

theorem analyticBoundary_eq :
    analyticBoundary X Z = Set.range (supportInclusion X Z) \ Set.range (regularInclusion X Z) := by
  rw [supportInclusion_range, regularInclusion_range]
  exact congrArg (fun S : Set X.left => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' S)
    (ComplexPoints.Analytic.SupportRegularBoundary.supportSingularBoundary_eq_sdiff Z X.hom)

theorem regularInclusion_subset : Set.range (regularInclusion X Z) ⊆ Set.range (supportInclusion X Z) := by
  rw [supportInclusion_range, regularInclusion_range]
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [← Geometric.GenericPoint.range_reducedSupportι Z]
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ Set.range (Geometric.GenericPoint.reducedSupportι Z)
  rw [← hy]
  exact ⟨Geometric.SmoothStratum.smoothStratumι (Geometric.SupportFiniteType.supportStructureMap Z X.hom) y, rfl⟩

theorem regularInclusion_avoids_boundary (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (regularOver X Z)) :
    regularInclusion X Z x ∉ analyticBoundary X Z := by
  rw [analyticBoundary_eq]
  exact fun h => h.2 (Set.mem_range_self x)

/-- The open ambient manifold where the regular support is actually closed. -/
def regularAmbientOpen : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  ⟨(analyticBoundary X Z)ᶜ, (analyticBoundary_closed X Z).isOpen_compl⟩

def regularComplementInclusion : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (regularOver X Z) → regularAmbientOpen X Z :=
  Set.codRestrict (regularInclusion X Z) (analyticBoundary X Z)ᶜ (regularInclusion_avoids_boundary X Z)

theorem regularComplementInclusion_range :
    Set.range (regularComplementInclusion X Z) = Subtype.val ⁻¹' Set.range (supportInclusion X Z) :=
  ComplexPoints.Analytic.RegularLocusComplement.range_codRestrict_complement_of_boundary (regularInclusion X Z) (Set.range (supportInclusion X Z))
    (analyticBoundary X Z) (regularInclusion_subset X Z) (analyticBoundary_eq X Z)
    (regularInclusion_avoids_boundary X Z)

theorem regularComplementInclusion_closed : Topology.IsClosedEmbedding (regularComplementInclusion X Z) :=
  ComplexPoints.Analytic.RegularLocusComplement.isClosedEmbedding_codRestrict_complement_of_boundary (regularInclusion X Z)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (regularToAmbient X Z))
    (Set.range (supportInclusion X Z)) (analyticBoundary X Z)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (supportToAmbient X Z)).isClosed_range
    (regularInclusion_subset X Z) (analyticBoundary_eq X Z) (regularInclusion_avoids_boundary X Z)

theorem regularDimension_eq :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension (regularOver X Z).hom =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom :=
  (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension (regularOver X Z).hom).symm.trans
    (Geometric.StratumDimension.smoothStratum_dimension_eq_support Z X.hom)

variable [IsIntegral X.left] [Smooth X.hom]

local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

theorem regularComplementInclusion_contMDiff (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, regularModel X Z) 𝓘(ℂ, E) r (regularComplementInclusion X Z) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (regularAmbientOpen X Z) (regularComplementInclusion X Z) r).mp
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (regularToAmbient X Z) r

theorem regularComplementInclusion_mfderiv_injective (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (regularOver X Z)) :
    Function.Injective (mfderiv 𝓘(ℂ, regularModel X Z) 𝓘(ℂ, E) (regularComplementInclusion X Z) x) := by
  have he := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := regularModel X Z) (F := E)
    (regularAmbientOpen X Z) (regularComplementInclusion X Z) x
  exact (congrArg (fun L : regularModel X Z →L[ℂ] E => Function.Injective L) he).mpr
    (ComplexPoints.Analytic.IntrinsicSmoothImmersion.mfderiv_nativeScheme_immersion_injective (regularToAmbient X Z) x)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport
