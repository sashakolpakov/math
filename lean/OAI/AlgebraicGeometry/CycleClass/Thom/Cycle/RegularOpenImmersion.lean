import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement
import OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph
import OAI.AlgebraicGeometry.CycleClass.Geometric.Span
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition

/-! # Regular Open Immersion -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions
open _root_.CategoryTheory
open _root_.TopologicalSpace
open scoped _root_.Manifold
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport
open OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions
section

/-! The actual regular part of a cycle is a closed holomorphic immersion on every ambient open contained in its regular ambient locus. -/

open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ D.regularAmbientOpen)

def regularOpenHomeomorph : RegularNeighborhoodDetection.Constructions.regularNeighborhood D U ≃ₜ U where
  toFun x := ⟨x.val.val, x.property⟩
  invFun y := ⟨⟨y.val, hU y.property⟩, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem regularOpenHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, V.analyticModel) ω (regularOpenHomeomorph D U hU) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U _ ω).mp
  exact (show ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, V.analyticModel) ω
    (Subtype.val : D.regularAmbientSpace → V.analyticSpace) from contMDiff_subtype_val).comp
      (show ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, V.analyticModel) ω
        (Subtype.val : RegularNeighborhoodDetection.Constructions.regularNeighborhood D U → D.regularAmbientSpace) from contMDiff_subtype_val)

theorem regularOpenHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, V.analyticModel) ω (regularOpenHomeomorph D U hU).symm := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) _ ω).mp
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff D.regularAmbientOpen _ ω).mp
  exact (show ContMDiff 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, V.analyticModel) ω
    (Subtype.val : U → V.analyticSpace) from contMDiff_subtype_val)

def regularOpenImmersion :
    GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) → U :=
  regularOpenHomeomorph D U hU ∘ GraphOpenImmersion.Constructions.restrictedBase D.regularComplementInclusion
    (D.contMDiff_regularComplementInclusion ω) (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U)

theorem regularOpenImmersion_analytic :
    ContMDiff 𝓘(ℂ, D.regularAnalyticModel) 𝓘(ℂ, V.analyticModel) ω (regularOpenImmersion D U hU) :=
  (regularOpenHomeomorph_analytic D U hU).comp
    (GraphOpenImmersion.Constructions.restrictedBase_analytic D.regularComplementInclusion
      (D.contMDiff_regularComplementInclusion ω) (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U))

theorem regularOpenImmersion_differential_injective
    (x : GraphOpenImmersion.Constructions.graphSourceOpen D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
      (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U)) :
    Function.Injective (mfderiv 𝓘(ℂ, D.regularAnalyticModel) 𝓘(ℂ, V.analyticModel)
      (regularOpenImmersion D U hU) x) := by
  have he := (regularOpenHomeomorph_analytic D U hU).mdifferentiable (by simp)
  have hei := (regularOpenHomeomorph_symm_analytic D U hU).mdifferentiable (by simp)
  unfold regularOpenImmersion
  rw [mfderiv_comp x (he _) ((GraphOpenImmersion.Constructions.restrictedBase_analytic D.regularComplementInclusion
    (D.contMDiff_regularComplementInclusion ω) (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U)).mdifferentiable (by simp) x)]
  exact (HolomorphicHomeomorph.Constructions.homeomorph_mfderiv_bijective (regularOpenHomeomorph D U hU) he hei _).injective.comp
    (OpenImmersion.Constructions.Raw.restrictedBase_differential_injective D.regularComplementInclusion
      (D.contMDiff_regularComplementInclusion ω) (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U)
      D.mfderiv_regularComplementInclusion_injective x)

theorem regularOpenImmersion_closedEmbedding : Topology.IsClosedEmbedding (regularOpenImmersion D U hU) :=
  (regularOpenHomeomorph D U hU).isClosedEmbedding.comp
    (OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding D.regularComplementInclusion
      (D.contMDiff_regularComplementInclusion ω) (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U)
      D.isClosedEmbedding_regularComplementInclusion)

theorem regularOpenImmersion_range : Set.range (regularOpenImmersion D U hU) =
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hx : D.regularComplementInclusion x.val ∈ Set.range D.regularComplementInclusion := Set.mem_range_self _
    rw [D.range_regularComplementInclusion] at hx
    exact hx
  · intro hy
    let z : D.regularAmbientSpace := ⟨y.val, hU y.property⟩
    have hz : z ∈ Set.range D.regularComplementInclusion := by
      rw [D.range_regularComplementInclusion]
      exact hy
    obtain ⟨x, hx⟩ := hz
    have hxU : D.regularComplementInclusion x ∈ RegularNeighborhoodDetection.Constructions.regularNeighborhood D U := by
      change (D.regularComplementInclusion x).val ∈ U
      rw [hx]
      exact y.property
    refine ⟨⟨x, hxU⟩, ?_⟩
    apply Subtype.ext
    change (D.regularComplementInclusion x).val = y.val
    exact congrArg Subtype.val hx

theorem regularOpenImmersion_mapsTo : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
    (Set.range (regularOpenImmersion D U hU))ᶜ (Set.range D.analyticInclusion)ᶜ := by
  intro y hy
  change y.val ∉ Set.range D.analyticInclusion
  rw [regularOpenImmersion_range] at hy
  exact hy

end

/-! Restriction of the original supported cycle class to any ambient open in the regular locus is the actual Thom class of the restricted regular immersion. -/

open scoped ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ D.regularAmbientOpen)

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

def regularOpenToRegular : TopCat.of U ⟶ TopCat.of D.regularAmbientSpace :=
  Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) (regularOpenHomeomorph D U hU)

theorem regularOpenToRegular_mapsTo : Set.MapsTo (regularOpenToRegular D U hU)
    (Set.range (regularOpenImmersion D U hU))ᶜ (Set.range D.regularComplementInclusion)ᶜ :=
  Open.ImageComplement.Constructions.ThomAmbientTransport.transportedOpenMap_mapsTo D.regularComplementInclusion (D.contMDiff_regularComplementInclusion ω)
    (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) (regularOpenHomeomorph D U hU)

theorem regularOpenToRegular_factor : regularOpenToRegular D U hU ≫
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) D.analyticSingularBoundaryᶜ =
      Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace) := rfl

theorem regularOpenThom_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (regularOpenToRegular D U hU)
      (regularOpenToRegular_mapsTo D U hU) (2 * p) D.regularThomClass =
      Degree.Constructions.ThomClass.complexThomClassInDegree (regularOpenImmersion D U hU) (regularOpenImmersion_analytic D U hU)
        (regularOpenImmersion_differential_injective D U hU) (regularOpenImmersion_closedEmbedding D U hU)
        p D.regularComplement_complexImmersionCodimension := by
  exact Open.ImageComplement.Constructions.ThomAmbientTransport.ThomClass_open_ambientTransport D.regularComplementInclusion
    (D.contMDiff_regularComplementInclusion ω) (RegularNeighborhoodDetection.Constructions.regularNeighborhood D U) (regularOpenHomeomorph D U hU)
    D.mfderiv_regularComplementInclusion_injective D.isClosedEmbedding_regularComplementInclusion
    ((regularOpenHomeomorph_analytic D U hU).mdifferentiable (by simp))
    ((regularOpenHomeomorph_symm_analytic D U hU).mdifferentiable (by simp))
    (regularOpenImmersion_analytic D U hU) (regularOpenImmersion_differential_injective D U hU)
    p D.regularComplement_complexImmersionCodimension D.regularComplement_complexImmersionCodimension

theorem supportedCycleClass_regularOpen_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
      (regularOpenImmersion_mapsTo D U hU) (2 * p) D.rationalSupportedCycleClass =
      Degree.Constructions.ThomClass.complexThomClassInDegree (regularOpenImmersion D U hU) (regularOpenImmersion_analytic D U hU)
        (regularOpenImmersion_differential_injective D U hU) (regularOpenImmersion_closedEmbedding D U hU)
        p D.regularComplement_complexImmersionCodimension := by
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (regularOpenToRegular D U hU)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) D.analyticSingularBoundaryᶜ)
      (regularOpenToRegular_mapsTo D U hU)
      (fun x hx => (D.mem_regularThomComplement_iff x).mp hx) (2 * p)) D.rationalSupportedCycleClass
  have h₂ := ConcreteCategory.congr_hom
    (ThomOpenRestriction.Constructions.pairMap_congr (regularOpenToRegular_factor D U hU)
      (fun x hx => (D.mem_regularThomComplement_iff _).mp (regularOpenToRegular_mapsTo D U hU hx))
      (regularOpenImmersion_mapsTo D U hU) (2 * p)) D.rationalSupportedCycleClass
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (regularOpenToRegular D U hU)
    (regularOpenToRegular_mapsTo D U hU) (2 * p)
    (D.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p) D.rationalSupportedCycleClass) = _ at h₁
  rw [D.rationalSupportedCycleClass_regularPullback] at h₁
  exact h₂.symm.trans (h₁.symm.trans (regularOpenThom_pullback D U hU))

end AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions.Bundle

/-! The actual regular part of a cycle on an ambient open, bundled
for the supported Thom composition theorem. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens V.analyticSpace) (hU : (U : Set V.analyticSpace) ⊆ Z.regularAmbientOpen)

abbrev cycleOpenImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (SmoothImmersion.Constructions.projectiveManifold V) U) p where
  regularComplexDimension := Z.regularComplexDimension
  regularAnalyticSpace := TopCat.of (GraphOpenImmersion.Constructions.graphSourceOpen Z.regularComplementInclusion
    (Z.contMDiff_regularComplementInclusion ω) (RegularNeighborhoodDetection.Constructions.regularNeighborhood Z U))
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := TopCat.ofHom
    ⟨regularOpenImmersion Z U hU, (regularOpenImmersion_analytic Z U hU).continuous⟩
  holomorphic := regularOpenImmersion_analytic Z U hU
  differential_injective := regularOpenImmersion_differential_injective Z U hU
  closed := regularOpenImmersion_closedEmbedding Z U hU
  regularComplexDimension_add_codimension := Z.regularComplexDimension_add_codimension

theorem cycleOpenImmersion_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
      (regularOpenImmersion_mapsTo Z U hU) (2 * p) Z.rationalSupportedCycleClass =
      (cycleOpenImmersion Z U hU).regularThomClass :=
  supportedCycleClass_regularOpen_Thom Z U hU

end AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions.Bundle

end

end OAI
