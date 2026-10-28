import OAI.RepresentationTheory.Theta.Geometric.SheafTransitionSplitting
import OAI.RepresentationTheory.Theta.Geometric.SmoothCocyclePrimitive
import Mathlib.Geometry.Manifold.Sheaf.Smooth

/-! # Smooth Sheaf -/

namespace OAI.RepresentationTheory.Theta.Geometric.SmoothSheaf

noncomputable section

/-! Positive-degree-one cohomology of the actual smooth function sheaf
vanishes on a compact smooth manifold, by splitting its finite local cocycle. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.TopologicalSpace Opposite Set
open scoped _root_.Manifold ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

abbrev smoothComplexFunctionSheaf : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M) :=
  smoothSheafAddCommGroup 𝓘(ℝ, E) 𝓘(ℝ, ℂ) M ℂ

theorem smoothComplexFunctionSheaf_H1_zero
    (v : CategoryTheory.Sheaf.H (smoothComplexFunctionSheaf E M) 1) : v = 0 := by
  classical
  let F := smoothComplexFunctionSheaf E M
  let S := AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence F
  have hS : S.ShortExact := AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact F
  obtain ⟨t, ht⟩ := AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafInjectiveCokernelBoundary_surjective F v
  let : Epi S.g := hS.epi_g
  let l : AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.SheafLocalLiftCover S.g t := AlgebraicGeometry.DivisorClass.Chern.Sheaf.CohomologyLifts.sheafLocalLiftCover S.g t
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (l.domain i : Set M)) (fun i => (l.domain i).isOpen) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, l.mem_domain x⟩)
  let U : s → Opens M := fun i => l.domain i.val
  have hU (x : M) : ∃ i : s, x ∈ U i := by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact ⟨⟨i, hi⟩, hxi⟩
  let g : ∀ i j : s, SmoothCocyclePrimitive.SmoothOpenScalar E (U i ⊓ U j) :=
    fun i j => l.transition hS i.val j.val
  have hg : ∀ i j k : s, ∀ (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k),
      g i j ⟨x, hi, hj⟩ + g j k ⟨x, hj, hk⟩ = g i k ⟨x, hi, hk⟩ := by
    intro i j k x hi hj hk
    have H := l.transition_cocycle hS i.val j.val k.val
    exact congrArg (fun f : SmoothCocyclePrimitive.SmoothOpenScalar E ((U i ⊓ U j) ⊓ U k) =>
      f ⟨x, ⟨hi, hj⟩, hk⟩) H
  obtain ⟨r, hr⟩ := SmoothCocyclePrimitive.exists_smooth_additive_cocycle_primitive U hU g hg
  have hc : (⊤ : Opens M) ≤ ⨆ i, U i := by
    intro x _
    obtain ⟨i, hi⟩ := hU x
    exact (le_iSup U i) hi
  have hsplit : ∀ i j : s, l.transition hS i.val j.val =
      AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ inf_le_right (r j) -
        AlgebraicGeometry.DivisorClass.Chern.Sheaf.TransitionCocycle.sheafSectionRestrict S.X₁ inf_le_left (r i) := by
    intro i j
    apply ContMDiffMap.ext
    intro x
    exact (hr i j x.val x.property.1 x.property.2).symm
  obtain ⟨w, hw⟩ := SheafTransitionSplitting.exists_globalLift_of_transition_split hS l Subtype.val hc r hsplit
  rw [← ht, ← hw]
  exact SheafTransitionSplitting.injectiveCokernelBoundary_image_zero F w

end

end OAI.RepresentationTheory.Theta.Geometric.SmoothSheaf
