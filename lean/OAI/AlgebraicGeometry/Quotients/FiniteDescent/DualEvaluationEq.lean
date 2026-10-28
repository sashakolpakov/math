import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualLine
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Evaluation

/-! # Dual Evaluation Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualEvaluationEq.Construction.DualEvaluationFrames

noncomputable section

/-! Evaluation against the dual is invertible in every rank-one frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective.Evaluation.SheafOfModules
open scoped TensorProduct

universe u

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

local instance : ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) := fun V => by
  change IsMulCommutative (X.presheaf.obj V)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

/-- A frame on the over-site identifies sections over its terminal open with scalars. -/
def coordinates (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (op (Over.mk (𝟙 U)))).mapIso e).toLinearEquiv

def dualCoordinates (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Γ(SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  SheafCohomology.Projective.Dual.SheafOfModules.dualTrivializationLinearEquiv X.ringCatSheaf M U e

/-- The value of a functional is the product of its dual coordinate and the
coordinate of the section. -/
theorem eval_eq (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : Γ(M, U)) (φ : Γ(SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M, U)) :
    SheafCohomology.Projective.Evaluation.SheafOfModules.evalSection X.ringCatSheaf M U φ m =
      coordinates M U e m * dualCoordinates M U e φ := by
  let T : Over U := Over.mk (𝟙 U)
  let r : Γ(X, U) := coordinates M U e m
  let c := coordinates M U e
  have hm : m = r • c.symm (1 : Γ(X, U)) := by
    rw [← c.symm.map_smul, smul_eq_mul, mul_one]
    exact (c.symm_apply_apply m).symm
  let a : Γ(M, U) →ₗ[Γ(X, U)] Γ(X, U) := (φ.val.app (op T)).hom
  change a (M.val.map (𝟙 U).op m) = r * a (c.symm (1 : Γ(X, U)))
  rw [op_id, M.val.map_id]
  change a m = r * a (c.symm (1 : Γ(X, U)))
  rw [hm, a.map_smul]
  rfl

/-- In a frame, presheaf evaluation is the tensor product of two scalar
coordinate equivalences followed by multiplication. -/
def evaluationEquiv (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Γ(M, U) ⊗[Γ(X, U)] Γ(SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M, U)) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  (TensorProduct.congr (coordinates M U e)
    (dualCoordinates M U e)).trans
      (TensorProduct.lid Γ(X, U) Γ(X, U))

theorem evaluationEquiv_eq (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (t : Γ(M, U) ⊗[Γ(X, U)] Γ(SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M, U)) :
    evaluationEquiv M U e t = (SheafCohomology.Projective.Evaluation.Scheme.Modules.evPre M).app (op U) t := by
  induction t using TensorProduct.inductionOn with
  | tmul m φ => exact (eval_eq M U e m φ).symm
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, h₁, h₂]
    exact (map_add ((SheafCohomology.Projective.Evaluation.Scheme.Modules.evPre M).app (op U)).hom t₁ t₂).symm

theorem bijective (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Function.Bijective ((SheafCohomology.Projective.Evaluation.Scheme.Modules.evPre M).app (op U)) := by
  have h : ⇑((SheafCohomology.Projective.Evaluation.Scheme.Modules.evPre M).app (op U)) = ⇑(evaluationEquiv M U e) := by
    funext t
    exact (evaluationEquiv_eq M U e t).symm
  rw [h]
  exact (evaluationEquiv M U e).bijective

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DualEvaluationEq.Construction.DualEvaluationFrames
