import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.BaseChangeNaturality

/-! # Base Change Presentation Relations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseChangePresentationRelations

noncomputable section

/-! The old relation module generates the kernel of the actual base-changed
presentation. The map and its formula use the same relation units as the
obstruction comparison. -/

open TensorProduct

universe u v w t z
variable {B : Type u} [CommRing B] (A : Type v) [CommRing A] [Algebra B A]
variable {F : Type w} [AddCommGroup F] [Module B F]
variable {M : Type t} [AddCommGroup M] [Module B M]

def baseChangePresentationRelationMap (q : F →ₗ[B] M) :
    A ⊗[B] q.ker →ₗ[A] (q.baseChange A).ker :=
  (q.ker.subtype.baseChange A).codRestrict _ (fun x => by
    induction x with
    | tmul a r =>
      change a ⊗ₜ[B] q r.val = 0
      rw [r.property, TensorProduct.tmul_zero]
    | add x y hx hy =>
      simp only [LinearMap.mem_ker] at hx hy
      change q.baseChange A (q.ker.subtype.baseChange A (x + y)) = 0
      simp only [map_add, hx, hy, add_zero])

theorem baseChangePresentationRelationMap_tmul (q : F →ₗ[B] M) (a : A) (z : q.ker) :
    baseChangePresentationRelationMap A q (a ⊗ₜ[B] z) =
      a • IdealTensor.BaseChangeNaturality.baseChangePresentationRelationUnit B A q z := by
  apply Subtype.ext
  change a ⊗ₜ[B] z.val = a • ((1 : A) ⊗ₜ[B] z.val)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem baseChangePresentationRelationMap_surjective (q : F →ₗ[B] M)
    (hq : Function.Surjective q) : Function.Surjective (baseChangePresentationRelationMap A q) := by
  intro z
  obtain ⟨x, hx⟩ := (lTensor_exact A q.exact_subtype_ker_map hq z.val).mp z.property
  exact ⟨x, Subtype.ext hx⟩

variable {N : Type z} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower B A N]

def extendModuleScalarMap (h : F →ₗ[B] N) : A ⊗[B] F →ₗ[A] N :=
  AlgebraTensorModule.lift (LinearMap.toSpanSingleton A (F →ₗ[B] N) h)

theorem extendModuleScalarMap_tmul (h : F →ₗ[B] N) (a : A) (x : F) :
    extendModuleScalarMap A h (a ⊗ₜ[B] x) = a • h x := rfl

theorem baseChange_relation_extension
    (q : F →ₗ[B] M) (hq : Function.Surjective q)
    (l : (q.baseChange A).ker →ₗ[A] N) (h : F →ₗ[B] N)
    (hh : ∀ z : q.ker, h z.val = l (IdealTensor.BaseChangeNaturality.baseChangePresentationRelationUnit B A q z))
    (z : (q.baseChange A).ker) :
    extendModuleScalarMap A h z.val = l z := by
  obtain ⟨x, rfl⟩ := baseChangePresentationRelationMap_surjective A q hq z
  induction x with
  | tmul a r =>
    change a • h r.val = l (baseChangePresentationRelationMap A q (a ⊗ₜ[B] r))
    rw [baseChangePresentationRelationMap_tmul, map_smul, hh r]
  | add x y hx hy =>
    simp only [map_add, AddMemClass.coe_add, hx, hy]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseChangePresentationRelations
