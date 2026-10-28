import Mathlib.RingTheory.Grassmannian

/-! # Linear Transport -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.LinearTransport

noncomputable section

/-! Transport actual finite projective Grassmannian quotients along a
linear isomorphism of their ambient modules. -/

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N] {k : ℕ}

def grassmannianLinearTransport (e : M ≃ₗ[R] N) (Q : Module.Grassmannian R M k) :
    Module.Grassmannian R N k where
  toSubmodule := Q.toSubmodule.map e.toLinearMap
  finite_quotient := Module.Finite.equiv (Submodule.Quotient.equiv Q.toSubmodule
    (Q.toSubmodule.map e.toLinearMap) e rfl)
  projective_quotient := Module.Projective.of_equiv (Submodule.Quotient.equiv Q.toSubmodule
    (Q.toSubmodule.map e.toLinearMap) e rfl)
  rankAtStalk_eq p := (congrFun (Module.rankAtStalk_eq_of_equiv (Submodule.Quotient.equiv Q.toSubmodule
    (Q.toSubmodule.map e.toLinearMap) e rfl)) p).symm.trans (Q.rankAtStalk_eq p)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.LinearTransport
