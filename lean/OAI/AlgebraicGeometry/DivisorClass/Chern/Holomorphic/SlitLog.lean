import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential

/-! # Slit Log -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SlitLog

noncomputable section

/-! Holomorphic logarithms on actual slit-plane domains, including restriction of unit sections. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

def holomorphicSlitLog (g : Exponential.HolomorphicFunction (E := E) (M := M)) (c : ℂ)
    (h : ∀ x, g x / c ∈ Complex.slitPlane) : Exponential.HolomorphicFunction (E := E) (M := M) where
  val x := Complex.log (g x / c) + Complex.log c
  property := by
    intro x
    have hr : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ∞ (fun y : M => g y / c) x := by
      simpa only [div_eq_mul_inv] using! (g.property.mul contMDiff_const).contMDiffAt
    exact ((Complex.contDiffAt_log (h x)).contMDiffAt.comp x hr).add contMDiffAt_const

theorem exp_holomorphicSlitLog (g : Exponential.HolomorphicFunction (E := E) (M := M)) (c : ℂ)
    (h : ∀ x, g x / c ∈ Complex.slitPlane) (hc : c ≠ 0) (x : M) :
    Complex.exp (holomorphicSlitLog g c h x) = g x := by
  change Complex.exp (Complex.log (g x / c) + Complex.log c) = g x
  rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (h x)),
    Complex.exp_log hc, div_mul_cancel₀ _ hc]

theorem holomorphicUnit_value_ne_zero (u : (Exponential.HolomorphicFunction (E := E) (M := M))ˣ) (x : M) :
    (u : Exponential.HolomorphicFunction (E := E) (M := M)) x ≠ 0 := by
  have h := congrArg (fun f : Exponential.HolomorphicFunction (E := E) (M := M) => f x) u.val_inv
  change (u : Exponential.HolomorphicFunction (E := E) (M := M)) x *
    (↑(u⁻¹) : Exponential.HolomorphicFunction (E := E) (M := M)) x = 1 at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem holomorphicExpUnit_slitLog (u : (Exponential.HolomorphicFunction (E := E) (M := M))ˣ) (c : ℂ)
    (h : ∀ x, (u : Exponential.HolomorphicFunction (E := E) (M := M)) x / c ∈ Complex.slitPlane) (hc : c ≠ 0) :
    Exponential.holomorphicExpUnit (holomorphicSlitLog (u : Exponential.HolomorphicFunction (E := E) (M := M)) c h) = u := by
  apply Units.ext
  apply ContMDiffMap.ext
  intro x
  exact exp_holomorphicSlitLog _ c h hc x

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SlitLog
