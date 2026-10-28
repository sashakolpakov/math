import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportNeighborhoodDetection
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Regular Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.RegularOpen.BundleCycles

noncomputable section

/-! The actual regular part of a cycle is a closed holomorphic immersion on every ambient open contained in its regular ambient locus. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImageComplement.Constructions.ThomAmbientTransport
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

theorem holomorphicHomeomorph_mfderiv_bijective
    {M N E F : Type} [TopologicalSpace M] [TopologicalSpace N]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [ChartedSpace E M] [ChartedSpace F N] (e : M ≃ₜ N)
    (he : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) e)
    (hi : MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E) e.symm) (x : M) :
    Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) e x) := by
  have hd : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) :=
    ⟨he.mdifferentiableOn, hi.mdifferentiableOn⟩
  exact hd.mfderiv_bijective (by trivial)

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (Z : IrreducibleCloseds X.left) (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⊆ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)

local notation "E" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

def schemeCycleRegularOpenHomeomorph : Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U ≃ₜ U where
  toFun x := ⟨x.val.val, x.property⟩
  invFun y := ⟨⟨y.val, hU y.property⟩, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycleRegularOpenHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (schemeCycleRegularOpenHomeomorph X Z U hU) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U _ ω).mp
  exact (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (Subtype.val : (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z) → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) from contMDiff_subtype_val).comp
      (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
        (Subtype.val : Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U → (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z)) from contMDiff_subtype_val)

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycleRegularOpenHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (schemeCycleRegularOpenHomeomorph X Z U hU).symm := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U) _ ω).mp
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z) _ ω).mp
  exact (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω
    (Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) from contMDiff_subtype_val)

def schemeCycleRegularOpenImmersion :
    CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U) → U :=
  schemeCycleRegularOpenHomeomorph X Z U hU ∘ CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω) (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U)

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycleRegularOpenImmersion_analytic :
    ContMDiff 𝓘(ℂ, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z) 𝓘(ℂ, E) ω (schemeCycleRegularOpenImmersion X Z U hU) :=
  (schemeCycleRegularOpenHomeomorph_analytic X Z U hU).comp
    (CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase_analytic (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z)
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω) (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U))

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycleRegularOpenImmersion_differential_injective
    (x : CycleClass.Thom.GraphOpenImmersion.Constructions.graphSourceOpen (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω)
      (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U)) :
    Function.Injective (mfderiv 𝓘(ℂ, CycleClass.Thom.Scheme.RegularSupport.Constructions.regularModel X Z) 𝓘(ℂ, E)
      (schemeCycleRegularOpenImmersion X Z U hU) x) := by
  have he := (schemeCycleRegularOpenHomeomorph_analytic X Z U hU).mdifferentiable (by simp)
  have hei := (schemeCycleRegularOpenHomeomorph_symm_analytic X Z U hU).mdifferentiable (by simp)
  unfold schemeCycleRegularOpenImmersion
  rw [mfderiv_comp x (he _) ((CycleClass.Thom.GraphOpenImmersion.Constructions.restrictedBase_analytic (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z)
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω) (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U)).mdifferentiable (by simp) x)]
  exact (holomorphicHomeomorph_mfderiv_bijective (schemeCycleRegularOpenHomeomorph X Z U hU) he hei _).injective.comp
    (CycleClass.Thom.OpenImmersion.Constructions.Raw.restrictedBase_differential_injective (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z)
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω) (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U)
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_mfderiv_injective X Z) x)

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycleRegularOpenImmersion_closedEmbedding : Topology.IsClosedEmbedding (schemeCycleRegularOpenImmersion X Z U hU) :=
  (schemeCycleRegularOpenHomeomorph X Z U hU).isClosedEmbedding.comp
    (CycleClass.Thom.OpenImmersion.Constructions.Raw.restrictedBase_closedEmbedding (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z)
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_contMDiff X Z ω) (Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U)
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_closed X Z))

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycleRegularOpenImmersion_range : Set.range (schemeCycleRegularOpenImmersion X Z U hU) =
    (Subtype.val : U → (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hx : (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) x.val ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) := Set.mem_range_self _
    rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_range X Z] at hx
    exact hx
  · intro hy
    let z : (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X Z) := ⟨y.val, hU y.property⟩
    have hz : z ∈ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) := by
      rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion_range X Z]
      exact hy
    obtain ⟨x, hx⟩ := hz
    have hxU : (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) x ∈ Scheme.SupportNeighborhoodDetection.BundleCycles.schemeSupportRegularNeighborhood X Z U := by
      change ((CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) x).val ∈ U
      rw [hx]
      exact y.property
    refine ⟨⟨x, hxU⟩, ?_⟩
    apply Subtype.ext
    change ((CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X Z) x).val = y.val
    exact congrArg Subtype.val hx

omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeCycleRegularOpenImmersion_mapsTo : Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (Set.range (schemeCycleRegularOpenImmersion X Z U hU))ᶜ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ := by
  intro y hy
  change y.val ∉ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z)
  rw [schemeCycleRegularOpenImmersion_range] at hy
  exact hy

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.RegularOpen.BundleCycles
