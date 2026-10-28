import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseChangePresentationRelations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AnnihilatedPresentationCriterion
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Base Change Reduced Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseChangeReducedPresentation

noncomputable section

/-! An extension of the residual relation map splits the reduced
base-changed presentation and kills its ideal-tensor obstruction. -/

open TensorProduct

universe u v w t z
variable {B : Type u} [CommRing B] (A : Type v) [CommRing A] [Algebra B A]
variable {F : Type w} [AddCommGroup F] [Module B F] [Module.Flat B F]
variable {M : Type t} [AddCommGroup M] [Module B M]
variable {N : Type z} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower B A N]

theorem baseChange_idealTensor_injective_of_relation_extension
    (q : F →ₗ[B] M) (hq : Function.Surjective q) (I : Ideal B)
    (l : (q.baseChange A).ker →ₗ[A] N)
    (hl : l.ker = I.map (algebraMap B A) • (⊤ : Submodule A (q.baseChange A).ker))
    (hN : Module.IsTorsionBySet A N (I.map (algebraMap B A)))
    (h : F →ₗ[B] N)
    (hh : ∀ z : q.ker, h z.val = l (IdealTensor.BaseChangeNaturality.baseChangePresentationRelationUnit B A q z)) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication A A (A ⊗[B] M) (I.map (algebraMap B A))) := by
  let qA := q.baseChange A
  let IA := I.map (algebraMap B A)
  have hqA : Function.Surjective qA := LinearMap.lTensor_surjective A hq
  exact AnnihilatedPresentationCriterion.presentation_idealTensor_injective_of_annihilated_extension qA hqA IA
    l hl hN (BaseChangePresentationRelations.extendModuleScalarMap A h) (BaseChangePresentationRelations.baseChange_relation_extension A q hq l h hh)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseChangeReducedPresentation
