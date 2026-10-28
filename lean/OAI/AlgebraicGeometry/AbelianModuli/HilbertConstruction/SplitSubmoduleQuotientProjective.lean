import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Projection

/-! # Split Submodule Quotient Projective -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitSubmoduleQuotientProjective

noncomputable section

/-! The quotient by a retract of a projective module is projective. -/
universe u v

theorem quotient_projective_of_submodule_retraction
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (P : Submodule R M) (r : M →ₗ[R] P) (hr : r.comp P.subtype = LinearMap.id) :
    Module.Projective R (M ⧸ P) := by
  have hc : IsCompl P r.ker := LinearMap.isCompl_of_proj (fun x => LinearMap.congr_fun hr x)
  have : Module.Projective R r.ker := Module.Projective.of_split r.ker.subtype
    (r.ker.projectionOnto P hc.symm) (Submodule.projectionOnto_comp_subtype hc.symm)
  exact Module.Projective.of_equiv (P.quotientEquivOfIsCompl r.ker hc).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitSubmoduleQuotientProjective
