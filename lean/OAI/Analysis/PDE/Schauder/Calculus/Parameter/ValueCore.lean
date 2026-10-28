import OAI.Analysis.PDE.Schauder.Calculus.TransformedBackground

/-! Pointwise physical Hessian evaluation, independent of parameter and lattice types. -/
noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {X : Type*} [MetricSpace X] {α : ℝ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance parameterCoreDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance parameterCoreDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance parameterCoreSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterCoreSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterCoreEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance parameterCoreEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance parameterCoreMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance parameterCoreMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem transformedBackgroundHessianField_eq_composition (hα : 0 ≤ α)
    (B₀ : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (T : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (p : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (B : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (u₀ u : E → ℝ) (Ψ : E → E) (x : X) (y z : E)
    (hu₀ : ContDiffAt ℝ 2 u₀ z) (hu : ContDiffAt ℝ 2 u y)
    (hΨ : ContDiffAt ℝ 2 Ψ z) (hinv : Ψ z = y)
    (hB₀ : OAI.Analysis.Normed.Function.Holder.HolderMap.value B₀ x = fderiv ℝ (fderiv ℝ u₀) z)
    (hJ : OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ Ψ z)
    (hT : OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ Ψ) z)
    (hp : OAI.Analysis.Normed.Function.Holder.HolderMap.value p x = fderiv ℝ u y)
    (hB : OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (fderiv ℝ u) y) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
      (B₀ + transformedHessianField hα J T p B)) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z => u₀ z+u (Ψ z)) z := by
  change OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j =>
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value B₀ x + OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedHessianField hα J T p B) x)
      (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) = _
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  congr 1
  funext i j
  have hu' : ContDiffAt ℝ 2 u (Ψ z) := by simpa only [hinv] using hu
  have hadd : fderiv ℝ (fderiv ℝ (fun z => u₀ z+u (Ψ z))) z =
      fderiv ℝ (fderiv ℝ u₀) z+fderiv ℝ (fderiv ℝ (fun z => u (Ψ z))) z := by
    simpa only [Function.comp_def] using! second_fderiv_add_at hu₀ (hu'.comp z hΨ)
  rw [hadd]
  simp only [add_apply,value_transformedHessianField,hB₀,hJ,hT,hp,hB]
  congr 1
  simpa only [hinv] using! (OAI.Analysis.PDE.Elliptic.second_fderiv_comp hu' hΨ
    (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)).symm

end OAI.Analysis.PDE.Schauder
