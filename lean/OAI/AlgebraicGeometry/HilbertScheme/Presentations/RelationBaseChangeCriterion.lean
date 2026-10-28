import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseChangeReducedPresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueLinearExtension

/-! # Relation Base Change Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RelationBaseChangeCriterion

noncomputable section

/-! Residue-field linear extension turns vanishing of old relations
into injectivity for the extended ideal, with an abstract residual module. -/

open TensorProduct

universe u v w t z
variable {B : Type u} [CommRing B] (A : Type v) [CommRing A] [Algebra B A]
variable {F : Type w} [AddCommGroup F] [Module B F] [Module.Flat B F]
variable {M : Type t} [AddCommGroup M] [Module B M]
variable {N : Type z} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower B A N]

theorem baseChange_idealTensor_injective_of_residue_relations
    (q : F →ₗ[B] M) (hq : Function.Surjective q) (I : Ideal B) [I.IsMaximal]
    (l : (q.baseChange A).ker →ₗ[A] N)
    (hl : l.ker = I.map (algebraMap B A) • (⊤ : Submodule A (q.baseChange A).ker))
    (hN : Module.IsTorsionBySet A N (I.map (algebraMap B A)))
    (hrel : ∀ z : q.ker, z.val ∈ I • (⊤ : Submodule B F) →
      l (IdealTensor.BaseChangeNaturality.baseChangePresentationRelationUnit B A q z) = 0) :
    Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication A A (A ⊗[B] M) (I.map (algebraMap B A))) := by
  have hT : Module.IsTorsionBySet B N I := by
    intro x r
    change r.val • x = 0
    rw [← algebraMap_smul A r.val x]
    exact hN (a := ⟨algebraMap B A r.val, Ideal.mem_map_of_mem _ r.property⟩)
  let : Module (B ⧸ I) N := hT.module
  let : IsScalarTower B (B ⧸ I) N := hT.isScalarTower
  let g : q.ker →ₗ[B] N := (l.restrictScalars B).comp (IdealTensor.BaseChangeNaturality.baseChangePresentationRelationUnit B A q)
  obtain ⟨h, hh⟩ := ResidueLinearExtension.residue_linear_extension I q.ker.subtype g hrel
  exact BaseChangeReducedPresentation.baseChange_idealTensor_injective_of_relation_extension A q hq I l hl hN h hh

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RelationBaseChangeCriterion
