import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Algebra.Hom

/-! # Integral Basis Intertwining -/

namespace OAI.RepresentationTheory.Theta.Geometric.IntegralBasisIntertwining

noncomputable section

/-! Equality on the actual integral number-field basis determines
intertwining for the complete rationally extended field action. -/

variable {E V W : Type} [Field E] [NumberField E]
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

 theorem integralBasis_fieldAction_intertwining
    (a : E →ₐ[ℚ] Module.End ℚ V) (b : E →ₐ[ℚ] Module.End ℚ W) (f : V →ₗ[ℚ] W)
    (h : ∀ i v, b (NumberField.integralBasis E i) (f v) = f (a (NumberField.integralBasis E i) v))
    (e : E) (v : V) : b e (f v) = f (a e v) := by
  let l : E →ₗ[ℚ] W := {
    toFun e := b e (f v)
    map_add' x y := by rw [map_add, LinearMap.add_apply]
    map_smul' r x := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  let r : E →ₗ[ℚ] V := {
    toFun e := a e v
    map_add' x y := by rw [map_add, LinearMap.add_apply]
    map_smul' q x := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have he : l = f.comp r := (NumberField.integralBasis E).ext (fun i => h i v)
  exact LinearMap.congr_fun he e

end

end OAI.RepresentationTheory.Theta.Geometric.IntegralBasisIntertwining
