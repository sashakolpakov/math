import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultOpen

/-! # Dolbeault Zero Kernel Map -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultZeroKernelMap

noncomputable section

/-! A complex-linear inclusion of original holomorphic functions with the exact Dolbeault kernel. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem openDolbeaultD_restrict {U V : Opens E} (h : V ≤ U) {n : ℕ} (form : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h (DolbeaultOpen.openDolbeaultD n form) =
      DolbeaultOpen.openDolbeaultD n (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h form) := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  have hd := (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.extension_restrict_eventuallyEq h form x).fderiv_eq (𝕜 := ℝ)
  change Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime form.extension (x : E) =
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict h form).extension (x : E)
  unfold Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
  rw [hd]

def holomorphicZeroFormLinear (U : Opens E) :
    Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U) →ₗ[ℂ] Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 where
  toFun := DolbeaultOpen.holomorphicFunctionZeroForm
  map_add' f g := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change DolbeaultOpen.holomorphicFunctionZeroForm (f + g) x v =
      DolbeaultOpen.holomorphicFunctionZeroForm f x v + DolbeaultOpen.holomorphicFunctionZeroForm g x v
    rw [DolbeaultOpen.holomorphicFunctionZeroForm_apply, DolbeaultOpen.holomorphicFunctionZeroForm_apply,
      DolbeaultOpen.holomorphicFunctionZeroForm_apply]
    rfl
  map_smul' c f := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change DolbeaultOpen.holomorphicFunctionZeroForm (c • f) x v = c • DolbeaultOpen.holomorphicFunctionZeroForm f x v
    rw [DolbeaultOpen.holomorphicFunctionZeroForm_apply, DolbeaultOpen.holomorphicFunctionZeroForm_apply]
    rfl

theorem holomorphicZeroFormLinear_injective (U : Opens E) :
    Function.Injective (holomorphicZeroFormLinear U) := by
  intro f g h
  apply ContMDiffMap.ext
  intro x
  have hv := congrArg (fun a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 0 => a x 0) h
  change DolbeaultOpen.holomorphicFunctionZeroForm f x 0 = DolbeaultOpen.holomorphicFunctionZeroForm g x 0 at hv
  rw [DolbeaultOpen.holomorphicFunctionZeroForm_apply, DolbeaultOpen.holomorphicFunctionZeroForm_apply] at hv
  exact hv

theorem holomorphicZeroFormLinear_d (U : Opens E) (f : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U)) :
    DolbeaultOpen.openDolbeaultD 0 (holomorphicZeroFormLinear U f) = 0 := by
  apply (DolbeaultOpen.openDolbeaultD_zero_iff _).mpr
  exact DolbeaultOpen.holomorphicFunctionZeroForm_dbar f

variable [FiniteDimensional ℂ E]

theorem holomorphicZeroFormLinear_range (U : Opens E) :
    LinearMap.range (holomorphicZeroFormLinear U) = LinearMap.ker (DolbeaultOpen.openDolbeaultD (U := U) 0) := by
  ext form
  constructor
  · rintro ⟨f, rfl⟩
    exact holomorphicZeroFormLinear_d U f
  · intro h
    exact ⟨DolbeaultOpen.holomorphicFunctionOfDbarZero form ((DolbeaultOpen.openDolbeaultD_zero_iff form).mp h),
      DolbeaultOpen.holomorphicFunctionZeroForm_ofDbarZero form ((DolbeaultOpen.openDolbeaultD_zero_iff form).mp h)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultZeroKernelMap
