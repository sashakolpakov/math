import OAI.AlgebraicGeometry.CycleClass.Geometric.GlobalSupportPurity
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Metrizable.Basic

/-! # Immersion Purity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ImmersionPurity

noncomputable section

/-!
# ChernClass: support purity on arbitrary open restrictions of a complex immersion

Restricting a closed complex immersion to an open subset of its ambient
manifold preserves its genuine injective differential. The existing support
purity theorem therefore applies to every such open restriction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Set Filter
open OAI.AlgebraicGeometry.CycleClass.Geometric.GlobalSupportPurity.Cycles
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section OpenTangent

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The local inverse of an open inclusion is complex smoothly differentiable. -/
theorem complexOpenInverse_contMDiffAt (U : Opens M) (hU : Nonempty U)
    {x : M} (hx : x ∈ (U : Set M)) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (U.openPartialHomeomorphSubtypeCoe hU).symm x := by
  rw [← ContMDiffAt.subtypeVal_comp_iff]
  apply contMDiffAt_id.congr_of_eventuallyEq
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv
    (by simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hy)

/-- The actual open inclusion has an invertible complex tangent map. -/
def complexOpenTangentEquiv (U : Opens M) (x : U) :
    TangentSpace 𝓘(ℂ, E) x ≃L[ℂ] TangentSpace 𝓘(ℂ, E) (x : M) := by
  have h : (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E) := by
    constructor
    · exact (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (U := U) (n := ω)).mdifferentiable
        (by simp) |>.mdifferentiableOn
    · intro y hy
      have hyU : y ∈ (U : Set M) := by simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hy
      exact ((complexOpenInverse_contMDiffAt U ⟨x⟩ hyU).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  exact h.mfderiv (by trivial)

theorem complexOpenTangentEquiv_coe (U : Opens M) (x : U) :
    (complexOpenTangentEquiv U x).toContinuousLinearMap =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (Subtype.val : U → M) x := rfl

end OpenTangent

variable {E F M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

variable (f : M → N) (hf : Topology.IsClosedEmbedding f)
    (hs : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hdf : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x)) (U : Opens N)

/-- The inverse image is an actual open submanifold. -/
def immersionOpenDomain : Opens M := ⟨f ⁻¹' U, U.isOpen.preimage hf.continuous⟩

/-- The restricted map has its actual open source and open target. -/
def immersionOpenMap : immersionOpenDomain f hf U → U := fun x => ⟨f x.val, x.property⟩

include hs in
/-- Analyticity of the actual restriction in both source and target. -/
theorem immersionOpenMap_contMDiff :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω (immersionOpenMap f hf U) := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U (immersionOpenMap f hf U) ω).mp
  exact hs.comp (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (U := immersionOpenDomain f hf U))

include hs hdf in
/-- Its differential is injective, by the actual derivative of open inclusion. -/
theorem immersionOpenMap_mfderiv_injective (x : immersionOpenDomain f hf U) :
    Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) (immersionOpenMap f hf U) x) := by
  have hj : Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F)
      (f ∘ (Subtype.val : immersionOpenDomain f hf U → M)) x) := by
    have hsub := ((contMDiff_subtype_val (I := 𝓘(ℂ, E))
      (U := immersionOpenDomain f hf U) (n := ω)) x).mdifferentiableAt (by simp)
    rw [mfderiv_comp x ((hs x.val).mdifferentiableAt (by simp))
      hsub]
    exact (hdf x.val).comp (complexOpenTangentEquiv (immersionOpenDomain f hf U) x).injective
  have he := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) (E := E) (F := F) U (immersionOpenMap f hf U) x
  intro v w hvw
  apply hj
  exact (congrArg (fun A : E →L[ℂ] F => A v) he).symm.trans
    (hvw.trans (congrArg (fun A : E →L[ℂ] F => A w) he))

/-- The restriction is still a closed embedding. -/
theorem immersionOpenMap_isClosedEmbedding : Topology.IsClosedEmbedding (immersionOpenMap f hf U) :=
  (U : Set N).restrictPreimage_isClosedEmbedding hf

/-- The restricted image is exactly the portion of the original support inside the open set. -/
theorem immersionOpenMap_range :
    Set.range (immersionOpenMap f hf U) = {x : U | x.val ∈ Set.range f} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨y, show f y ∈ U from hy.symm ▸ x.property⟩, Subtype.ext hy⟩

variable [hFinE : FiniteDimensional ℂ E] [hFinF : FiniteDimensional ℂ F]
  [hManM : IsManifold 𝓘(ℂ, E) ω M] [hManN : IsManifold 𝓘(ℂ, F) ω N] [hMetric : MetrizableSpace N]

include hf hs hdf hFinE hFinF hManM hManN hMetric in
/-- Actual singular support cohomology vanishes on every ambient open subset
below the real normal codimension. -/
theorem closedComplexImmersion_open_supportCohomology_isZero (n : ℕ)
    (hn : n < 2 * (Module.finrank ℂ F - Module.finrank ℂ E)) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | x.val ∈ Set.range f}ᶜ n) := by
  let : MetrizableSpace U := MetrizableSpace.subtype (U : Set N)
  rw [← immersionOpenMap_range f hf U]
  exact CycleClass.Geometric.GlobalSupportPurity.Cycles.closedComplexImmersion_supportCohomology_isZero
    (immersionOpenMap f hf U) (immersionOpenMap_isClosedEmbedding f hf U)
    (immersionOpenMap_contMDiff f hf hs U) (immersionOpenMap_mfderiv_injective f hf hs hdf U) n hn

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ImmersionPurity
