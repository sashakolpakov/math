import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Hessian
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.ValueCore

open Set Module
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {U : Set Z}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "D" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local instance parameterValueDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance parameterValueDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance parameterValueSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterValueSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance parameterValueEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance parameterValueEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance parameterValueMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance parameterValueMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

omit [Fintype ι] in
theorem ParameterJetFields.mooreOperator_value
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    (z : Z) (v : D) (B₀ u : E → ℝ) (Ψ : E → E) (x : {x | r x ≤ 0}) (y : E)
    (hB₀ : ContDiffAt ℝ 2 B₀ y) (hu : ContDiffAt ℝ 2 u x)
    (hi : ContDiffAt ℝ 2 Ψ y) (hinv : Ψ y = x)
    (hBg : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z) x = fderiv ℝ (fderiv ℝ B₀) y)
    (hJ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z) x = fderiv ℝ Ψ y)
    (hK : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z) x = fderiv ℝ (fderiv ℝ Ψ) y)
    (hD₁ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (J.first v) x = fderiv ℝ u x)
    (hD₂ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (J.second v) x = fderiv ℝ (fderiv ℝ u) x) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.mooreOperator J hα (z,v)) x =
      OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y + u (Ψ y)) y) -
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z) x := by
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value (transformedBackgroundMooreField hα (C.background z)
    (C.jacobian z) (C.curvature z) (J.first v) (J.second v)) x - _ = _
  congr 1
  exact transformedBackgroundMooreField_eq_composition hα _ _ _ _ _ B₀ u Ψ x x y
    hB₀ hu hi hinv hBg hJ hK hD₁ hD₂

omit [Fintype ι] in
theorem ParameterJetFields.hessianField_value
    (C : ParameterJetFields r α U e b) (J : LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    (z : Z) (v : D) (B₀ u : E → ℝ) (Ψ : E → E) (x : {x | r x ≤ 0}) (y : E)
    (hB₀ : ContDiffAt ℝ 2 B₀ y) (hu : ContDiffAt ℝ 2 u x)
    (hi : ContDiffAt ℝ 2 Ψ y) (hinv : Ψ y = x)
    (hBg : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z) x = fderiv ℝ (fderiv ℝ B₀) y)
    (hJ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z) x = fderiv ℝ Ψ y)
    (hK : OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z) x = fderiv ℝ (fderiv ℝ Ψ) y)
    (hD₁ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (J.first v) x = fderiv ℝ u x)
    (hD₂ : OAI.Analysis.Normed.Function.Holder.HolderMap.value (J.second v) x = fderiv ℝ (fderiv ℝ u) x) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.hessianField J hα (z,v)) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y + u (Ψ y)) y := by
  exact transformedBackgroundHessianField_eq_composition hα (C.background z)
    (C.jacobian z) (C.curvature z) (J.first v) (J.second v) B₀ u Ψ x x y
    hB₀ hu hi hinv hBg hJ hK hD₁ hD₂

end OAI.Analysis.PDE.Schauder
