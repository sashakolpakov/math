import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Algebra.Basic

/-! # Action Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ActionTransport

noncomputable section

/-! Transporting an action through a chart and its conormal dual
comparison preserves the specified generator operators. -/

variable {R k U V W O I : Type} [CommRing R] [CommRing k] [Algebra R k]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module R W] [CommRing O]
  (t : U ≃ₗ[k] V) (e : U ≃ₗ[k] (W →ₗ[R] k)) (ρ : O →+* Module.End k V)

def transportedDualAction : O →+* Module.End k (W →ₗ[R] k) :=
  (t.symm.trans e).conjRingEquiv.toRingHom.comp ρ

theorem transportedDualAction_apply (a : O) (ℓ : W →ₗ[R] k) :
    transportedDualAction t e ρ a ℓ = e (t.symm (ρ a (t (e.symm ℓ)))) := rfl

theorem transportedDualAction_generator (a : I → O) (d : I → Module.End k U)
    (c : I → Module.End R W)
    (ht : ∀ i u, ρ (a i) (t u) = t (d i u))
    (he : ∀ i u, e (d i u) = (e u).comp (c i))
    (i : I) (ℓ : W →ₗ[R] k) :
    transportedDualAction t e ρ (a i) ℓ = ℓ.comp (c i) := by
  rw [transportedDualAction_apply, ht, t.symm_apply_apply, he, e.apply_symm_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ActionTransport
