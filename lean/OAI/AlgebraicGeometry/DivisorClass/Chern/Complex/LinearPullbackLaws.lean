import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearOpenPullback
import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarDolbeaultCommutation

/-! # Linear Pullback Laws -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearPullbackLaws

noncomputable section

/-! Actual complex-linear open pullbacks compose, invert, and preserve scalar zero-forms. -/

open _root_.ContinuousAlternatingMap _root_.TopologicalSpace Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E F G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  {U : Opens E} {V : Opens F} {W : Opens G} {n : ℕ}

theorem complexLinearOpenPullback_comp (L : E →L[ℂ] F) (K : F →L[ℂ] G)
    (hL : MapsTo L (U : Set E) (V : Set F)) (hK : MapsTo K (V : Set F) (W : Set G))
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W n) :
    LinearOpenPullback.complexLinearOpenPullback L hL (LinearOpenPullback.complexLinearOpenPullback K hK a) =
      LinearOpenPullback.complexLinearOpenPullback (K.comp L) (hK.comp hL) a := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rw [LinearOpenPullback.complexLinearOpenPullback_apply, LinearOpenPullback.complexLinearOpenPullback_apply, LinearOpenPullback.complexLinearOpenPullback_apply]
  ext v
  rfl

theorem complexLinearOpenPullback_inverse (e : E ≃L[ℂ] F)
    (h : MapsTo e (U : Set E) (V : Set F)) (hi : MapsTo e.symm (V : Set F) (U : Set E))
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm V n) :
    LinearOpenPullback.complexLinearOpenPullback e.symm.toContinuousLinearMap hi
      (LinearOpenPullback.complexLinearOpenPullback e.toContinuousLinearMap h a) = a := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rw [LinearOpenPullback.complexLinearOpenPullback_apply, LinearOpenPullback.complexLinearOpenPullback_apply]
  ext v
  change a ⟨e (e.symm x), h (hi x.property)⟩ (fun i => e (e.symm (v i))) = a x v
  simp only [e.apply_symm_apply]

theorem complexLinearOpenPullback_injective (e : E ≃L[ℂ] F)
    (h : MapsTo e (U : Set E) (V : Set F)) (hi : MapsTo e.symm (V : Set F) (U : Set E)) :
    Function.Injective (LinearOpenPullback.complexLinearOpenPullback (n := n) e.toContinuousLinearMap h) := by
  intro a b hab
  have hback := congrArg (LinearOpenPullback.complexLinearOpenPullback e.symm.toContinuousLinearMap hi) hab
  simpa only [complexLinearOpenPullback_inverse e h hi] using hback

theorem complexLinearOpenPullback_scalarZero (L : E →L[ℂ] F)
    (hL : MapsTo L (U : Set E) (V : Set F)) {f : F → ℂ}
    (hf : ContDiffOn ℝ ∞ f (V : Set F)) :
    LinearOpenPullback.complexLinearOpenPullback L hL (ScalarDolbeaultCommutation.scalarOpenZeroForm V f hf) =
      ScalarDolbeaultCommutation.scalarOpenZeroForm U (fun x => f (L x)) (hf.comp (L.restrictScalars ℝ).contDiff.contDiffOn hL) := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  rw [LinearOpenPullback.complexLinearOpenPullback_apply]
  ext v
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LinearPullbackLaws
