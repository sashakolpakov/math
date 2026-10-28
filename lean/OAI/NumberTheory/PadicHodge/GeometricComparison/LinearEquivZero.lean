import Mathlib.Algebra.Module.Equiv.Basic

/-! # Linear Equiv Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LinearEquivZero.LinearEquivReductionZero

/-! Transport through a linear equivalence respects a checked reduction
square, with compatibility hypotheses kept as linear-map equalities. -/

variable {R V W N P : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  (e : V ≃ₗ[R] W) (r : W →ₗ[R] N) (φ : W →ₗ[R] W) (b : N →ₗ[R] N)
  (f : P →ₗ[R] N) (d : V →ₗ[R] P)
  (hs : r.comp e.toLinearMap = f.comp d) (hr : b.comp r = r.comp φ)

include hs hr in
theorem reduction (x : V) :
    r (e ((e.symm.toLinearMap.comp (φ.comp e.toLinearMap)) x)) = b (f (d x)) :=
  (congrArg r (e.apply_symm_apply (φ (e x)))).trans
    ((LinearMap.congr_fun hr (e x)).symm.trans (congrArg b (LinearMap.congr_fun hs x)))

include hs hr in
theorem zero (x : V) (hz : b (f (d x)) = 0) :
    r (e ((e.symm.toLinearMap.comp (φ.comp e.toLinearMap)) x)) = 0 :=
  (reduction e r φ b f d hs hr x).trans hz

include hs hr in
theorem linearMap : r.comp (e.toLinearMap.comp (e.symm.toLinearMap.comp (φ.comp e.toLinearMap))) =
    b.comp (f.comp d) :=
  LinearMap.ext (reduction e r φ b f d hs hr)

end OAI.NumberTheory.PadicHodge.GeometricComparison.LinearEquivZero.LinearEquivReductionZero
