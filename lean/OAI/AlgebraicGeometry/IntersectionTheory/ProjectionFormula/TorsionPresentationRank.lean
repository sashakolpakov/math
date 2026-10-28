import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FreeSubmodule
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Torsion Presentation Rank -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TorsionPresentationRank

noncomputable section

/-! The two free modules in a torsion presentation differ in rank
by the rank of the actual relation kernel. -/

universe u v

theorem rank_eq (R : Type u) [CommRing R] [IsDomain R]
    (B C M : Type v) [AddCommGroup B] [AddCommGroup C] [AddCommGroup M]
    [Module R B] [Module R C] [Module R M]
    [Module.Finite R B] [Module.Finite R C] [Module.Finite R M]
    (g : B →ₗ[R] C) (π : C →ₗ[R] M) (he : Function.Exact g π)
    (hπ : Function.Surjective π) (hM : Module.IsTorsion R M) :
    Module.finrank R B = Module.finrank R g.ker + Module.finrank R C := by
  have hrange : g.range = π.ker := (LinearMap.exact_iff.mp he).symm
  let e : (C ⧸ g.range) ≃ₗ[R] M :=
    (Submodule.quotEquivOfEq _ _ hrange).trans (π.quotKerEquivOfSurjective hπ)
  have hc : Module.finrank R (C ⧸ g.range) = 0 := e.finrank_eq.trans hM.finrank_eq_zero
  have hgr := g.range.finrank_quotient_add_finrank
  rw [hc, zero_add] at hgr
  have hgk := g.ker.finrank_quotient_add_finrank
  rw [g.quotKerEquivRange.finrank_eq, hgr] at hgk
  omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TorsionPresentationRank
