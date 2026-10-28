import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Operator
import OAI.Analysis.PDE.Schauder.Calculus.MooreFieldDerivative

open Set
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {I : Set ℝ}
  {Φ : ℝ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4} {B₀ f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance deformationZeroDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance deformationZeroDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance deformationZeroEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance deformationZeroEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance deformationZeroSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance deformationZeroSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance deformationZeroMapGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance deformationZeroMapSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem DeformationFields.background_zero_eq_field
    (C : DeformationFields r α I Φ B₀ f) (hI : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    (hB : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (fderiv ℝ B₀) x) :
    C.background 0 = B := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  rw [C.background_value 0 hI,hΦ]
  exact (hB x).symm

theorem DeformationFields.jacobian_zero
    (C : DeformationFields r α I Φ B₀ f) (hI : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x) :
    C.jacobian 0 = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ E) := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  rw [C.jacobian_value 0 hI,OAI.Analysis.Normed.Function.Holder.HolderMap.value_constant,OAI.Analysis.PDE.Dirichlet.inverseJacobian_zero hΦ]

theorem DeformationFields.curvature_zero
    (C : DeformationFields r α I Φ B₀ f) (hI : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x) :
    C.curvature 0 = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0 := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  rw [C.curvature_value 0 hI,OAI.Analysis.Normed.Function.Holder.HolderMap.value_constant,OAI.Analysis.PDE.Dirichlet.inverseHessian_zero hΦ]

theorem DeformationFields.mooreOperator_zero
    (C : DeformationFields r α I Φ B₀ f) (hI : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x)
    (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α) (v : Z) :
    C.mooreOperator hα D₁ D₂ (0,v) =
      OAI.Analysis.Normed.Function.Holder.mooreDetField hα n (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)
        (C.background 0 + D₂ v)) - C.source 0 := by
  unfold DeformationFields.mooreOperator transformedBackgroundMooreField
  rw [C.jacobian_zero hI hΦ,C.curvature_zero hI hΦ,transformedHessianField_identity]

theorem DeformationFields.mooreOperator_zero_affine_general
    (C : DeformationFields r α I Φ B₀ f) (hI : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x)
    (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α) (v : Z) :
    C.mooreOperator hα D₁ D₂ (0,v) =
      OAI.Analysis.Normed.Function.Holder.mooreDetField hα n
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) (C.background 0) +
          ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp D₂) v) - C.source 0 := by
  rw [C.mooreOperator_zero hI hΦ hα D₁ D₂ v]
  congr 2
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).map_add _ _

theorem DeformationFields.hasFDerivAt_zero_general
    (C : DeformationFields r α I Φ B₀ f) (hI : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x)
    (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α) (v : Z) :
    HasFDerivAt (fun w => C.mooreOperator hα D₁ D₂ (0,w))
      ((fderiv ℝ (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n)
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) (C.background 0) +
          ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp D₂) v)).comp
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp D₂)) v := by
  have he : (fun w => C.mooreOperator hα D₁ D₂ (0,w)) =
      (fun w => OAI.Analysis.Normed.Function.Holder.mooreDetField hα n
        ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)) (C.background 0) +
          ((OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots)).comp D₂) w) - C.source 0) :=
    funext (fun w => C.mooreOperator_zero_affine_general hI hΦ hα D₁ D₂ w)
  rw [he]
  exact hasFDerivAt_mooreDetField_affine hα _ _ (C.source 0) v

theorem DeformationFields.mooreOperator_zero_of_field
    (C : DeformationFields r α I Φ B₀ f) (hI : 0 ∈ I) (hΦ : ∀ x, Φ (0,x) = x)
    (hα : 0 ≤ α)
    (D₁ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] ℝ) α)
    (D₂ : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α) (v : Z)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α)
    (hbase : C.background 0 + D₂ v = B)
    (heq : ∀ x, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value
      (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots) B) x) = f x) :
    C.mooreOperator hα D₁ D₂ (0,v) = 0 := by
  rw [C.mooreOperator_zero hI hΦ hα D₁ D₂ v,hbase]
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.Normed.Function.Holder.mooreDetField hα n
    (OAI.Analysis.Normed.Function.Holder.HolderMap.map (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots) B)) x -
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source 0) x = 0
  rw [OAI.Analysis.Normed.Function.Holder.value_mooreDetField,heq x,C.source_value 0 hI,hΦ,sub_self]

end OAI.Analysis.PDE.Schauder
