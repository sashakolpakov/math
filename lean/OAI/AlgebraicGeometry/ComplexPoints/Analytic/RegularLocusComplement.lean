import OAI.AlgebraicGeometry.ComplexPoints.Analytic.CycleStratumRealization
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SupportRegularBoundary
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! # Regular Locus Complement -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

noncomputable section

/-!
# The regular locus inside the complement of its singular boundary

Removing the singular boundary turns the actual regular-locus embedding into
a closed embedding in an open subset of the ambient analytic manifold.
-/

open scoped ContDiff _root_.Manifold _root_.Topology

section

section ClosedContainer

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

omit [TopologicalSpace M] [TopologicalSpace N] in
/-- Removing exactly the difference between a closed container and an
embedded range leaves that range as the container's intersection with the
open-complement subtype. This statement uses the actual codomain restriction. -/
theorem range_codRestrict_complement_of_boundary
    (f : M → N) (F C : Set N) (hsub : Set.range f ⊆ F)
    (hC : C = F \ Set.range f) (havoid : ∀ x, f x ∈ Cᶜ) :
    Set.range (Set.codRestrict f Cᶜ havoid) = Subtype.val ⁻¹' F := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact hsub ⟨x, rfl⟩
  · intro hy
    have hyrange : y.val ∈ Set.range f := by
      by_contra h
      apply y.property
      exact (congrArg (fun S : Set N => (y.val : N) ∈ S) hC).mpr ⟨hy, h⟩
    obtain ⟨x, hx⟩ := hyrange
    exact ⟨x, Subtype.ext hx⟩

/-- An embedding becomes closed after removing the precise boundary of its
range inside a closed container. No compactness or assumed closedness of the
original embedded range is needed. -/
theorem isClosedEmbedding_codRestrict_complement_of_boundary
    (f : M → N) (hf : Topology.IsEmbedding f)
    (F C : Set N) (hF : IsClosed F) (hsub : Set.range f ⊆ F)
    (hC : C = F \ Set.range f) (havoid : ∀ x, f x ∈ Cᶜ) :
    Topology.IsClosedEmbedding (Set.codRestrict f Cᶜ havoid) := by
  refine ⟨hf.codRestrict Cᶜ havoid, ?_⟩
  rw [range_codRestrict_complement_of_boundary f F C hsub hC havoid]
  exact hF.preimage continuous_subtype_val

end ClosedContainer

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace F N]

/-- Restricting a map's codomain to an actual open submanifold preserves every
order of smoothness, including analyticity, in the inherited charts. -/
theorem contMDiff_intoOpen_iff (U : TopologicalSpace.Opens N) (f : M → U) (r : ℕ∞ω) :
    ContMDiff (𝓘(𝕜, E)) (𝓘(𝕜, F)) r (Subtype.val ∘ f) ↔
      ContMDiff (𝓘(𝕜, E)) (𝓘(𝕜, F)) r f := by
  simp only [ContMDiff, ContMDiffAt, ContMDiffWithinAt,
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff]

/-- Differentiability also agrees under the genuine open codomain restriction. -/
theorem mdifferentiableAt_intoOpen_iff (U : TopologicalSpace.Opens N) (f : M → U) (x : M) :
    MDifferentiableAt (𝓘(𝕜, E)) (𝓘(𝕜, F)) (Subtype.val ∘ f) x ↔
      MDifferentiableAt (𝓘(𝕜, E)) (𝓘(𝕜, F)) f x := by
  simp only [MDifferentiableAt, ChartedSpace.LiftPropAt,
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff]

set_option backward.isDefEq.respectTransparency false in
/-- In the inherited open charts, the two actual manifold differentials
coincide after the standard identification with their model vector spaces. -/
theorem mfderiv_intoOpen_eq (U : TopologicalSpace.Opens N) (f : M → U) (x : M) :
    (show E →L[𝕜] F from mfderiv (𝓘(𝕜, E)) (𝓘(𝕜, F)) f x) =
      (show E →L[𝕜] F from mfderiv (𝓘(𝕜, E)) (𝓘(𝕜, F)) (Subtype.val ∘ f) x) := by
  unfold mfderiv
  rw [← mdifferentiableAt_intoOpen_iff U f x]
  rfl

end

namespace DimensionCycleSupport

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The actual open part of the ambient analytic variety obtained by deleting
the support's closed singular boundary. Its charts are the inherited open
submanifold charts of the ambient variety. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientOpen (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    TopologicalSpace.Opens V.analyticSpace :=
  ⟨Z.analyticSingularBoundaryᶜ, Z.isClosed_analyticSingularBoundary.isOpen_compl⟩

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientOpen_coe (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (Z.regularAmbientOpen : Set V.analyticSpace) = Z.analyticSingularBoundaryᶜ := rfl

/-- The genuine ambient open submanifold containing the support's regular
locus as a closed embedded subspace. -/
abbrev _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientSpace (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Type := Z.regularAmbientOpen

/-- The actual regular-locus point map, with codomain restricted to the
complement of the singular boundary. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularAnalyticSpace → Z.regularAmbientSpace :=
  fun x => ⟨Z.regularAnalyticToAmbient x, Z.regularAnalyticToAmbient_not_mem_boundary x⟩

instance _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientSpace_nonempty (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Nonempty Z.regularAmbientSpace :=
  Nonempty.map Z.regularComplementInclusion inferInstance

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementInclusion_val (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    (Z.regularComplementInclusion x).val = Z.regularAnalyticToAmbient x := rfl

/-- The restricted map has exactly the underlying algebraic point map. -/
@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.underlying_regularComplementInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    SchemePointHomeomorphs.schemeComplexPoints.underlying (Z.regularComplementInclusion x).val =
      Z.regularToAmbient.left (SchemePointHomeomorphs.schemeComplexPoints.underlying x) :=
  SchemePointHomeomorphs.schemeComplexPoints.underlying_map Z.regularToAmbient x

theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.continuous_regularComplementInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Continuous Z.regularComplementInclusion :=
  Z.continuous_regularAnalyticToAmbient.subtype_mk _

/-- The regular locus is precisely the part of the original support lying
inside the actual boundary complement. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_regularComplementInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Set.range Z.regularComplementInclusion =
      Subtype.val ⁻¹' Set.range Z.analyticInclusion :=
  range_codRestrict_complement_of_boundary Z.regularAnalyticToAmbient
    (Set.range Z.analyticInclusion) Z.analyticSingularBoundary
    Z.range_regularAnalyticToAmbient_subset Z.analyticSingularBoundary_eq_sdiff
    Z.regularAnalyticToAmbient_not_mem_boundary

/-- Deleting the singular boundary makes the genuine regular-locus map a
closed embedding for the ordinary analytic topology. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.isClosedEmbedding_regularComplementInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Topology.IsClosedEmbedding Z.regularComplementInclusion :=
  isClosedEmbedding_codRestrict_complement_of_boundary Z.regularAnalyticToAmbient
    Z.isEmbedding_regularAnalyticToAmbient (Set.range Z.analyticInclusion)
    Z.analyticSingularBoundary Z.isClosedEmbedding_analyticInclusion.isClosed_range
    Z.range_regularAnalyticToAmbient_subset Z.analyticSingularBoundary_eq_sdiff
    Z.regularAnalyticToAmbient_not_mem_boundary

local instance (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : IsIntegral Z.regularOver.left :=
  inferInstanceAs (IsIntegral Z.regularScheme)

local instance (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : Smooth Z.regularOver.hom :=
  inferInstanceAs (Smooth Z.regularToBase)

local instance : IsIntegral V.toOver.left := V.property
local instance : Smooth V.toOver.hom := V.presentation.smooth

/-- The actual codomain restriction is analytic in the inherited complex
manifold charts, and hence smooth to every order. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.contMDiff_regularComplementInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, Z.regularAnalyticModel)) (𝓘(ℂ, V.analyticModel)) r
      Z.regularComplementInclusion := by
  apply (contMDiff_intoOpen_iff Z.regularAmbientOpen Z.regularComplementInclusion r).mp
  exact IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map Z.regularToAmbient r

/-- The same map is smooth on the inherited underlying real manifolds. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.real_contMDiff_regularComplementInclusion (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℝ, Z.regularAnalyticModel)) (𝓘(ℝ, V.analyticModel)) r
      Z.regularComplementInclusion := by
  apply (contMDiff_intoOpen_iff Z.regularAmbientOpen Z.regularComplementInclusion r).mp
  exact IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map Z.regularToAmbient r

set_option backward.isDefEq.respectTransparency false in
/-- The differential of the closed embedding in the boundary complement is
exactly the previously established ambient complex differential. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.mfderiv_regularComplementInclusion_eq_ambient (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    (show Z.regularAnalyticModel →L[ℂ] V.analyticModel from
      mfderiv (𝓘(ℂ, Z.regularAnalyticModel)) (𝓘(ℂ, V.analyticModel))
        Z.regularComplementInclusion x) =
    (show Z.regularAnalyticModel →L[ℂ] V.analyticModel from
      mfderiv (𝓘(ℂ, Z.regularAnalyticModel)) (𝓘(ℂ, V.analyticModel))
        Z.regularAnalyticToAmbient x) :=
  mfderiv_intoOpen_eq Z.regularAmbientOpen Z.regularComplementInclusion x

set_option backward.isDefEq.respectTransparency false in
/-- The equality also holds for the actual real differentials, allowing the
real normal quotient to be carried into this open ambient manifold. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.real_mfderiv_regularComplementInclusion_eq_ambient (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    (show Z.regularAnalyticModel →L[ℝ] V.analyticModel from
      mfderiv (𝓘(ℝ, Z.regularAnalyticModel)) (𝓘(ℝ, V.analyticModel))
        Z.regularComplementInclusion x) =
    (show Z.regularAnalyticModel →L[ℝ] V.analyticModel from
      mfderiv (𝓘(ℝ, Z.regularAnalyticModel)) (𝓘(ℝ, V.analyticModel))
        Z.regularAnalyticToAmbient x) :=
  mfderiv_intoOpen_eq Z.regularAmbientOpen Z.regularComplementInclusion x

/-- The actual complex differential remains injective after restricting the
target to the open complement of the singular boundary. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.mfderiv_regularComplementInclusion_injective (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Function.Injective
      (mfderiv (𝓘(ℂ, Z.regularAnalyticModel)) (𝓘(ℂ, V.analyticModel))
        Z.regularComplementInclusion x) := by
  exact (congrArg (fun L : Z.regularAnalyticModel →L[ℂ] V.analyticModel =>
    Function.Injective L) (Z.mfderiv_regularComplementInclusion_eq_ambient x)).mpr
      (IntrinsicSmoothImmersion.mfderiv_nativeScheme_immersion_injective Z.regularToAmbient x)

/-- The actual underlying real differential of the closed regular-locus
embedding is injective as well. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.real_mfderiv_regularComplementInclusion_injective (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Function.Injective
      (mfderiv (𝓘(ℝ, Z.regularAnalyticModel)) (𝓘(ℝ, V.analyticModel))
        Z.regularComplementInclusion x) := by
  exact (congrArg (fun L : Z.regularAnalyticModel →L[ℝ] V.analyticModel =>
    Function.Injective L) (Z.real_mfderiv_regularComplementInclusion_eq_ambient x)).mpr
      (IntrinsicSmoothImmersion.real_mfderiv_nativeScheme_immersion_injective Z.regularToAmbient x)

end DimensionCycleSupport

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
