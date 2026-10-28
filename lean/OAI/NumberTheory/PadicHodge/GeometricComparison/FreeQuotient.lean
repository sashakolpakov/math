import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Module.Projective

/-! # Free Quotient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FreeQuotient.FreeQuotientComplement

noncomputable section

/-! A projective quotient supplies a genuine complement to the original submodule, over a general coefficient ring. -/

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem exists_complement (P : Submodule R M) [Module.Projective R (M ⧸ P)] :
    ∃ Q : Submodule R M, IsCompl P Q := by
  obtain ⟨s, hs⟩ := P.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr P.mkQ_surjective)
  let g : M →ₗ[R] P := (LinearMap.id - s.comp P.mkQ).codRestrict P (by
    intro x
    apply (Submodule.Quotient.mk_eq_zero P).mp
    change P.mkQ (x - s (P.mkQ x)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun hs (P.mkQ x)).symm)
  refine ⟨g.ker, LinearMap.isCompl_of_proj (f := g) ?_⟩
  intro x
  apply Subtype.ext
  change (x : M) - s (P.mkQ x) = (x : M)
  rw [show P.mkQ (x : M) = 0 from (Submodule.Quotient.mk_eq_zero P).mpr x.property, map_zero, sub_zero]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FreeQuotient.FreeQuotientComplement
