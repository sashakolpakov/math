import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivative
import OAI.Analysis.DifferentialForms.Manifold.Alternatization

/-! # Vectors -/

namespace OAI.Analysis.DifferentialForms.Manifold

/-!
# Pullback of smooth differential forms on normed spaces

The construction uses the actual derivative on every tangent argument and
commutes with mathlib's exterior derivative. It is local infrastructure for
forms on manifolds, not an asserted geometric comparison theorem.
-/

open scoped ContDiff

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n : ℕ}

/-- Pullback along a smooth map, complex-linear in the differential form. -/
noncomputable def Basic.SmoothForm.pullback (f : E → F) (hf : ContDiff ℝ ∞ f) :
    Basic.SmoothForm F n →ₗ[ℂ] Basic.SmoothForm E n where
  toFun form :=
    ⟨fun x => (form (f x)).compContinuousLinearMap (fderiv ℝ f x),
      Alternatization.contDiff_alternating_compContinuousLinearMap (form.smooth.comp hf)
        (contDiff_infty_iff_fderiv.mp hf).2⟩
  map_add' form otherForm := by
    apply Subtype.ext
    funext x
    ext v
    rfl
  map_smul' c form := by
    apply Subtype.ext
    funext x
    ext v
    rfl

@[simp] theorem Basic.SmoothForm.pullback_apply (f : E → F) (hf : ContDiff ℝ ∞ f)
    (form : Basic.SmoothForm F n) (x : E) :
    Basic.SmoothForm.pullback f hf form x = (form (f x)).compContinuousLinearMap (fderiv ℝ f x) := rfl

theorem Basic.SmoothForm.pullback_apply_vectors (f : E → F) (hf : ContDiff ℝ ∞ f)
    (form : Basic.SmoothForm F n) (x : E) (v : Fin n → E) :
    Basic.SmoothForm.pullback f hf form x v = form (f x) (fun i => fderiv ℝ f x (v i)) := rfl

@[simp] theorem Basic.SmoothForm.pullback_id (form : Basic.SmoothForm E n) :
    Basic.SmoothForm.pullback (id : E → E) contDiff_id form = form := by
  ext x v
  simp [Basic.SmoothForm.pullback_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]

theorem Basic.SmoothForm.pullback_comp (f : E → F) (hf : ContDiff ℝ ∞ f)
    (g : F → G) (hg : ContDiff ℝ ∞ g) (form : Basic.SmoothForm G n) :
    Basic.SmoothForm.pullback (g ∘ f) (hg.comp hf) form = Basic.SmoothForm.pullback f hf (Basic.SmoothForm.pullback g hg form) := by
  ext x v
  simp only [Basic.SmoothForm.pullback_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    fderiv_comp x ((hg.differentiable (by simp)).differentiableAt)
      ((hf.differentiable (by simp)).differentiableAt),
    ContinuousLinearMap.coe_comp, Function.comp_assoc, Function.comp_apply]

/-- Exterior differentiation commutes with pullback along a smooth map. -/
theorem Basic.SmoothForm.d_pullback (f : E → F) (hf : ContDiff ℝ ∞ f) (form : Basic.SmoothForm F n) :
    Basic.SmoothForm.d (Basic.SmoothForm.pullback f hf form) = Basic.SmoothForm.pullback f hf (Basic.SmoothForm.d form) := by
  apply Basic.SmoothForm.ext
  intro x
  exact extDeriv_pullback
    ((form.smooth.differentiable (by simp)).differentiableAt)
    hf.contDiffAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))

end OAI.Analysis.DifferentialForms.Manifold
