import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorRelations
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Annihilated Presentation Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AnnihilatedPresentationCriterion

noncomputable section

/-! A presentation splits modulo an ideal when its residual relation
map extends to an ideal-annihilated module. -/

universe u v w t
variable {B : Type u} [CommRing B]
variable {F : Type v} [AddCommGroup F] [Module B F]
variable {M : Type w} [AddCommGroup M] [Module B M]
variable {N : Type t} [AddCommGroup N] [Module B N]

theorem linearMap_zero_on_ideal_multiple (I : Ideal B) (hN : Module.IsTorsionBySet B N I)
    (h : F →ₗ[B] N) (x : F) (hx : x ∈ I • (⊤ : Submodule B F)) : h x = 0 := by
  refine Submodule.smul_induction_on hx (fun r hr v _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]
    exact hN (a := ⟨r, hr⟩)
  · rw [map_add, hx, hy, add_zero]

theorem presentation_idealTensor_injective_of_annihilated_extension [Module.Flat B F]
    (q : F →ₗ[B] M) (hq : Function.Surjective q) (I : Ideal B)
    (l : q.ker →ₗ[B] N) (hl : l.ker = I • (⊤ : Submodule B q.ker))
    (hN : Module.IsTorsionBySet B N I) (h : F →ₗ[B] N)
    (hh : ∀ z : q.ker, h z.val = l z) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M I) := by
  apply (Quotient.TensorRelations.presentation_idealTensor_injective_iff_relation_mem q hq I).mpr
  intro z hz
  rw [← hl]
  change l z = 0
  rw [← hh]
  exact linearMap_zero_on_ideal_multiple I hN h z.val hz

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AnnihilatedPresentationCriterion
