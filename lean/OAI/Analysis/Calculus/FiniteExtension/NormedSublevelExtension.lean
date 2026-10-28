import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Sublevel

/-! Finite-order regular-sublevel extension is invariant under a linear
change to Euclidean coordinates; in particular it applies to product spaces
equipped with the usual maximum norm. -/
noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.Calculus.FiniteExtension

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [Nontrivial X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_contDiff_extension_regular_sublevel_normed
    {N : ℕ} (r : X → ℝ) (hr : ContDiff ℝ ∞ r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (f : X → F) (hf : ContDiffOn ℝ N f {x | r x ≤ 0}) :
    ∃ g : X → F, ContDiff ℝ N g ∧ ∀ x, r x ≤ 0 → g x = f x := by
  let d := Module.finrank ℝ X
  have hd : 0 < d := Module.finrank_pos (R := ℝ) (M := X)
  let e : EuclideanSpace ℝ (Fin d) ≃L[ℝ] X :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [d])
  have hr' : ContDiff ℝ ∞ (fun y => r (e y)) := hr.comp e.contDiff
  have hreg' : ∀ y, r (e y) = 0 → fderiv ℝ (fun y => r (e y)) y ≠ 0 := by
    intro y hy hz
    have he : fderiv ℝ (fun y => r (e y)) y =
        (fderiv ℝ r (e y)).comp e.toContinuousLinearMap :=
      ((hr.differentiable (by simp) (e y)).hasFDerivAt.comp y
        e.toContinuousLinearMap.hasFDerivAt).fderiv
    apply hreg (e y) hy
    ext v
    have hv := congrArg (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => L (e.symm v)) hz
    rw [he] at hv
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply,zero_apply] using hv
  have hf' : ContDiffOn ℝ N (fun y => f (e y)) {y | r (e y) ≤ 0} :=
    hf.comp e.contDiff.contDiffOn (fun y hy => hy)
  obtain ⟨g,hg,hgf⟩ := exists_contDiff_extension_regular_sublevel hd
    (fun y => r (e y)) hr' hreg' (fun y => f (e y)) hf'
  refine ⟨fun x => g (e.symm x),hg.comp e.symm.contDiff,?_⟩
  intro x hx
  have hh := hgf (e.symm x) (by simpa only [e.apply_symm_apply] using hx)
  simpa only [e.apply_symm_apply] using hh

end OAI.Analysis.Calculus.FiniteExtension
