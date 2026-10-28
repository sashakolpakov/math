import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic

/-! # Homeomorph Inverse Differentiable -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomeomorphInverseDifferentiable

noncomputable section

section

/-! # An actual homeomorphism with bijective complex differential has differentiable inverse -/

open scoped _root_.Manifold

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem homeomorph_inverse_mDifferentiableAt (h : M ≃ₜ N) (x : M)
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) h x)
    (hb : Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) h x)) :
    MDifferentiableAt 𝓘(ℂ, F) 𝓘(ℂ, E) h.symm (h x) := by
  let e := ((chartAt E x).symm.trans h.toOpenPartialHomeomorph).trans (chartAt F (h x))
  have hd : DifferentiableAt ℂ e ((chartAt E x) x) := by
    simpa only [mfld_simps, writtenInExtChartAt, e, OpenPartialHomeomorph.coe_trans,
      differentiableWithinAt_univ, Function.comp_def] using
      hf.differentiableWithinAt_writtenInExtChartAt
  have hfb : Function.Bijective (fderiv ℂ e ((chartAt E x) x)) := by
    rw [hf.mfderiv] at hb
    simpa only [mfld_simps, writtenInExtChartAt, e, OpenPartialHomeomorph.coe_trans,
      fderivWithin_univ, Function.comp_def] using! hb
  let f' : E ≃L[ℂ] F := ContinuousLinearEquiv.ofBijective (fderiv ℂ e ((chartAt E x) x))
    (LinearMap.ker_eq_bot.mpr hfb.1) (LinearMap.range_eq_top.mpr hfb.2)
  have hs : (chartAt E x) x ∈ e.source := by
    simp [e]
  have hv : e ((chartAt E x) x) = (chartAt F (h x)) (h x) := by
    simp [e]
  have ht : (chartAt F (h x)) (h x) ∈ e.target := hv ▸ e.map_source hs
  have hi : e.symm ((chartAt F (h x)) (h x)) = (chartAt E x) x := by
    rw [← hv, e.left_inv hs]
  have he : HasFDerivAt e (f' : E →L[ℂ] F) (e.symm ((chartAt F (h x)) (h x))) := by
    rw [hi]
    exact hd.hasFDerivAt
  have hinv := e.hasFDerivAt_symm ht he
  refine (mdifferentiableAt_iff _ _).mpr ⟨h.symm.continuous.continuousAt, ?_⟩
  simpa only [mfld_simps, writtenInExtChartAt, e, OpenPartialHomeomorph.coe_trans,
    Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.symm_apply_apply,
    Function.comp_def] using hinv.differentiableAt.differentiableWithinAt

end

/-! # An actual open partial homeomorphism has differentiable inverse on its target -/

open scoped _root_.Manifold

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem partialHomeomorph_inverse_mDifferentiableAt (h : OpenPartialHomeomorph M N)
    (x : M) (hx : x ∈ h.source)
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, F) h x)
    (hb : Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) h x)) :
    MDifferentiableAt 𝓘(ℂ, F) 𝓘(ℂ, E) h.symm (h x) := by
  let e := ((chartAt E x).symm.trans h).trans (chartAt F (h x))
  have hd : DifferentiableAt ℂ e ((chartAt E x) x) := by
    simpa only [mfld_simps, writtenInExtChartAt, e, OpenPartialHomeomorph.coe_trans,
      differentiableWithinAt_univ, Function.comp_def] using
      hf.differentiableWithinAt_writtenInExtChartAt
  have hfb : Function.Bijective (fderiv ℂ e ((chartAt E x) x)) := by
    rw [hf.mfderiv] at hb
    simpa only [mfld_simps, writtenInExtChartAt, e, OpenPartialHomeomorph.coe_trans,
      fderivWithin_univ, Function.comp_def] using! hb
  let f' : E ≃L[ℂ] F := ContinuousLinearEquiv.ofBijective (fderiv ℂ e ((chartAt E x) x))
    (LinearMap.ker_eq_bot.mpr hfb.1) (LinearMap.range_eq_top.mpr hfb.2)
  have hs : (chartAt E x) x ∈ e.source := by
    simp [e, hx]
  have hv : e ((chartAt E x) x) = (chartAt F (h x)) (h x) := by
    simp [e]
  have ht : (chartAt F (h x)) (h x) ∈ e.target := hv ▸ e.map_source hs
  have hi : e.symm ((chartAt F (h x)) (h x)) = (chartAt E x) x := by
    rw [← hv, e.left_inv hs]
  have he : HasFDerivAt e (f' : E →L[ℂ] F) (e.symm ((chartAt F (h x)) (h x))) := by
    rw [hi]
    exact hd.hasFDerivAt
  have hinv := e.hasFDerivAt_symm ht he
  refine (mdifferentiableAt_iff _ _).mpr ⟨h.continuousAt_symm (h.map_source hx), ?_⟩
  simpa only [mfld_simps, writtenInExtChartAt, e, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm,
    h.left_inv hx,
    Function.comp_def] using hinv.differentiableAt.differentiableWithinAt

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomeomorphInverseDifferentiable
