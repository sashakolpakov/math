import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.IntrinsicEtale
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-! # Covering -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Covering.Constructions.Construction

noncomputable section

open scoped _root_.Manifold ContDiff

/-- Properness makes the discrete fibers of a local homeomorphism finite. -/
theorem finite_fiber_of_proper_localHomeomorph
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (f : M → N) (hp : IsProperMap f) (hl : IsLocalHomeomorph f) (y : N) :
    (f ⁻¹' {y}).Finite := by
  apply (hp.isCompact_preimage isCompact_singleton).finite
  apply hl.isLocalHomeomorphOn.isDiscrete_of_image
  have hs : (f '' (f ⁻¹' {y})).Subsingleton := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (show f x = y from hx).trans (show f z = y from hz).symm
  exact hs.isDiscrete

/-- A proper local homeomorphism from a Hausdorff space is a covering
map with finite fibers. This uses its actual open local inverses. -/
theorem covering_of_proper_localHomeomorph
    {M N : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace N]
    (f : M → N) (hp : IsProperMap f) (hl : IsLocalHomeomorph f) :
    IsCoveringMap f := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  exact hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun y _ => finite_fiber_of_proper_localHomeomorph f hp hl y) hl.isLocalHomeomorphOn

/-- In particular, a proper analytic local diffeomorphism is a finite
covering on the underlying topological spaces. -/
theorem covering_of_proper_localDiffeomorph
    {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (f : M → N) (hp : IsProperMap f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, E)) (𝓘(ℂ, F)) ω f) :
    IsCoveringMap f ∧ ∀ y, (f ⁻¹' {y}).Finite :=
  ⟨covering_of_proper_localHomeomorph f hp hl.isLocalHomeomorph,
    finite_fiber_of_proper_localHomeomorph f hp hl.isLocalHomeomorph⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Covering.Constructions.Construction
