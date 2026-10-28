import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential
import Mathlib.Topology.LocalAtTarget

/-! # Immersion Open Restriction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions

/-! Restricting an actual closed complex immersion to an ambient
open gives its actual source preimage and inherited analytic immersion. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : ComplexImmersion.Constructions.ClosedComplexImmersion V p) (U : Opens V.analyticSpace)

abbrev sourceOpen : Opens Z.regularAnalyticSpace :=
  ⟨Z.regularComplementInclusion ⁻¹' (U : Set V.analyticSpace),
    U.isOpen.preimage Z.continuous_regularComplementInclusion⟩

def restrictedMap : TopCat.of (sourceOpen Z U) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun y => ⟨Z.regularComplementInclusion y.val, y.property⟩,
    (Z.continuous_regularComplementInclusion.comp continuous_subtype_val).subtype_mk _⟩

theorem restrictedMap_analytic :
    ContMDiff 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel) ω (restrictedMap Z U) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U (restrictedMap Z U) ω).mp
  exact Z.holomorphic.comp (show ContMDiff 𝓘(ℂ, Z.regularAnalyticModel)
    𝓘(ℂ, Z.regularAnalyticModel) ω (Subtype.val : sourceOpen Z U → Z.regularAnalyticSpace) from
      contMDiff_subtype_val)

theorem restrictedMap_differential_injective (x : sourceOpen Z U) :
    Function.Injective (mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel)
      (restrictedMap Z U) x) := by
  have hv : MDifferentiableAt 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Z.regularAnalyticModel)
      (Subtype.val : sourceOpen Z U → Z.regularAnalyticSpace) x :=
    (show ContMDiff 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Z.regularAnalyticModel) 1
      (Subtype.val : sourceOpen Z U → Z.regularAnalyticSpace) from
        contMDiff_subtype_val).mdifferentiableAt one_ne_zero
  have hd := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := Z.regularAnalyticModel)
    (F := V.analyticModel) U (restrictedMap Z U) x
  change mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel) (restrictedMap Z U) x =
    mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel)
      (Z.regularComplementInclusion ∘ Subtype.val) x at hd
  rw [mfderiv_comp x ((Z.holomorphic x.val).mdifferentiableAt (by simp)) hv,
    Open.InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal] at hd
  exact (congrArg (fun L : Z.regularAnalyticModel →L[ℂ] V.analyticModel => Function.Injective L) hd).mpr
    (Z.differential_injective x.val)

def restrict : ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V U) p where
  regularComplexDimension := Z.regularComplexDimension
  regularAnalyticSpace := TopCat.of (sourceOpen Z U)
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := restrictedMap Z U
  holomorphic := restrictedMap_analytic Z U
  differential_injective := restrictedMap_differential_injective Z U
  closed := (U : Set V.analyticSpace).restrictPreimage_isClosedEmbedding Z.closed
  regularComplexDimension_add_codimension := Z.regularComplexDimension_add_codimension

end AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions.Support

/-! The image and complement of an open-restricted closed immersion
are the literal preimages of the original image and complement. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions

variable {V : ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : ComplexImmersion.Constructions.ClosedComplexImmersion V p) (U : Opens V.analyticSpace)

theorem restricted_range : Set.range (restrict Z U).regularComplementInclusion =
    Subtype.val ⁻¹' Set.range Z.regularComplementInclusion := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, rfl⟩
  · rintro ⟨x, hxy⟩
    have hxU : Z.regularComplementInclusion x ∈ U := hxy.symm ▸ y.property
    exact ⟨⟨x, hxU⟩, Subtype.ext hxy⟩

theorem restricted_complement :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace) (Set.range Z.regularComplementInclusion)ᶜ U =
      (Set.range (restrict Z U).regularComplementInclusion)ᶜ := by
  rw [restricted_range]
  rfl

end AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions.Support

end

end OAI
