import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Smooth Cover Functions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothCoverFunctions

noncomputable section

/-! Gluing compatible smooth real functions on an open cover indexed by its points. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (U : M → Opens M) (hU : ∀ x, x ∈ U x) (f : ∀ i, U i → ℝ)

def smoothCoverFunction : M → ℝ := fun x => f x ⟨x, hU x⟩

theorem smoothCoverFunction_onOpen
    (hf : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (i : M) (x : U i) : smoothCoverFunction U hU f x.val = f i x :=
  hf x.val i x.val (hU x.val) x.property

theorem smoothCoverFunction_contMDiff
    (hf : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j), f i ⟨x, hi⟩ = f j ⟨x, hj⟩)
    (hs : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f i)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (smoothCoverFunction U hU f) := by
  intro x
  apply (contMDiffAt_subtype_iff (U := U x) (x := ⟨x, hU x⟩)).mp
  have he : (fun y : U x => smoothCoverFunction U hU f y.val) = f x :=
    funext (smoothCoverFunction_onOpen U hU f hf x)
  rw [he]
  exact hs x ⟨x, hU x⟩

theorem smoothCoverFunction_pos (hf : ∀ i x, 0 < f i x) (x : M) :
    0 < smoothCoverFunction U hU f x := hf x ⟨x, hU x⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothCoverFunctions
