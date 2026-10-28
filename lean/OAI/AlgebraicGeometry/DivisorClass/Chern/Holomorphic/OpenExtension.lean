import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! # Open Extension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension

noncomputable section

/-! Extend holomorphic functions on an open set, retaining holomorphicity on that set. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

def holomorphicOpenExtend {U : Opens M} (g : Exponential.HolomorphicFunction (E := E) (M := U)) : M → ℂ := by
  classical
  exact fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 1

theorem holomorphicOpenExtend_apply {U : Opens M} (g : Exponential.HolomorphicFunction (E := E) (M := U))
    (x : M) (hx : x ∈ U) : holomorphicOpenExtend g x = g ⟨x, hx⟩ := by
  simp only [holomorphicOpenExtend, dite_eq_left hx]

theorem holomorphicOpenExtend_contMDiffOn {U : Opens M}
    (g : Exponential.HolomorphicFunction (E := E) (M := U)) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ) ∞ (holomorphicOpenExtend g) U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply (contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)).mp
  have he : (fun y : U => holomorphicOpenExtend g y.val) = g.val := by
    funext y
    exact holomorphicOpenExtend_apply g y y.property
  rw [he]
  exact g.property ⟨x, hx⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension
