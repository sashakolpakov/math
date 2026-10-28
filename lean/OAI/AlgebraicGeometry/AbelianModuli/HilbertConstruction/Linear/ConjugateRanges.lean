import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Conjugate Ranges -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ConjugateRanges

noncomputable section

/-! Conjugating an actual linear endomorphism transports its range by the same linear equivalence. -/
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {V : Type w} [AddCommGroup V] [Module R V]

def linearConjugateRangeEquiv (e : M ≃ₗ[R] V) (p : Module.End R V) :
    (e.symm.conjRingEquiv p).range ≃ₗ[R] p.range where
  toFun x := ⟨e x.val, by
    obtain ⟨y, hy⟩ := x.property
    refine ⟨e y, ?_⟩
    exact (e.apply_symm_apply (p (e y))).symm.trans (congrArg e hy)⟩
  invFun x := ⟨e.symm x.val, by
    obtain ⟨y, hy⟩ := x.property
    refine ⟨e.symm y, ?_⟩
    change e.symm (p (e (e.symm y))) = e.symm x.val
    rw [e.apply_symm_apply, hy]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' r x := Subtype.ext (e.map_smul r x.val)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ConjugateRanges
