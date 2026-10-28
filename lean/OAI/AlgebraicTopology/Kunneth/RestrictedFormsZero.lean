import OAI.AlgebraicTopology.Kunneth.RestrictedForms
import OAI.Analysis.DifferentialForms.Manifold.DegreeZero
import Mathlib.Analysis.Calculus.MeanValue

/-! # Restricted Forms Zero -/

namespace OAI.AlgebraicTopology.Kunneth.RestrictedFormsZero

noncomputable section

/-! The degree-zero kernel of restricted forms on a convex set is constant. -/

set_option backward.isDefEq.respectTransparency false

open Set

namespace Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance restrictedZeroFormsAddGroup (n : ℕ) : AddCommGroup (OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance
local instance restrictedZeroFormsModule (n : ℕ) : Module ℂ (OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E n) := inferInstance

def constantZeroForm (c : ℂ) : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 0 := (OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.const c).toZeroForm

@[simp] theorem constantZeroForm_apply (c : ℂ) (x : E) (v : Fin 0 → E) :
    constantZeroForm c x v = c := rfl

theorem zeroForm_constant_on_convex {S : Set E} (hS : UniqueDiffOn ℝ S)
    (hconvex : Convex ℝ S) (a : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm E 0)
    (ha : ∀ x ∈ S, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a x = 0) {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    a x = a y := by
  have hdf (z : E) (hz : z ∈ S) : fderiv ℝ (a.toSmoothFunction : E → ℂ) z = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    calc
      fderiv ℝ (a.toSmoothFunction : E → ℂ) z u =
          OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a.toSmoothFunction.toZeroForm z (fun _ => u) :=
        (OAI.Analysis.DifferentialForms.Manifold.Functions.SmoothFunction.d_toZeroForm_apply a.toSmoothFunction z (fun _ => u)).symm
      _ = 0 := by rw [a.toZeroForm_toSmoothFunction, ha z hz]; rfl
  have he : a.toSmoothFunction x = a.toSmoothFunction y :=
    hconvex.is_const_of_fderivWithin_eq_zero
      (a.toSmoothFunction.smooth.differentiable (by simp)).differentiableOn
      (fun z hz => (fderivWithin_eq_fderiv (hS z hz)
        (a.toSmoothFunction.smooth.differentiable (by simp) z)).trans (hdf z hz)) hx hy
  ext v
  have hv : v = (0 : Fin 0 → E) := Subsingleton.elim _ _
  rw [hv]
  exact he

theorem restrictedFormD_zero_constant {S : Set E} (hS : UniqueDiffOn ℝ S)
    (hconvex : Convex ℝ S) {x : E} (hx : x ∈ S) (a : RestrictedForms.Constructions.RestrictedForm S 0)
    (ha : RestrictedForms.Constructions.restrictedFormD hS 0 a = 0) :
    ∃ c : ℂ, a = RestrictedForms.Constructions.restrictForm S 0 (constantZeroForm c) := by
  obtain ⟨a, rfl⟩ := (RestrictedForms.Constructions.formsVanishingOn S 0).mkQ_surjective a
  change RestrictedForms.Constructions.restrictForm S 1 (OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a) = 0 at ha
  have ha' : ∀ y ∈ S, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d a y = 0 :=
    (Submodule.Quotient.mk_eq_zero (RestrictedForms.Constructions.formsVanishingOn S 1)).mp ha
  refine ⟨a x 0, (RestrictedForms.Constructions.restrictForm_eq_iff S 0 a (constantZeroForm (a x 0))).mpr ?_⟩
  intro y hy
  rw [zeroForm_constant_on_convex hS hconvex a ha' hy hx]
  ext v
  have hv : v = (0 : Fin 0 → E) := Subsingleton.elim _ _
  rw [hv]
  rfl

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.RestrictedFormsZero
