import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.BlockChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateChoices

/-! # Tate Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction

noncomputable section

/-!
Transport the geometric subgroup classification through an additive
coordinate equivalence of the actual native block points. Membership is
measured in the original relative subgroup, after its actual inclusion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

def subgroupAdditivePointsEquiv {G : Type*} [Group G] (J : Subgroup G) :
    Additive J ≃+ J.toAddSubgroup where
  toFun x := ⟨Additive.ofMul x.toMul.val, x.toMul.property⟩
  invFun x := Additive.ofMul ⟨x.val.toMul, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def typedSubgroupAdditiveEquiv {G M : Type*} [Group G] [AddGroup M] :
    {J : Subgroup G // Nonempty (J ≃* Multiplicative M)} ≃
      {J : AddSubgroup (Additive G) // Nonempty (J ≃+ M)} :=
  Subgroup.toAddSubgroup.toEquiv.subtypeEquiv (fun J => by
    exact ⟨fun ⟨e⟩ => ⟨(subgroupAdditivePointsEquiv J).symm.trans e.toAdditiveLeft⟩,
      fun ⟨e⟩ => ⟨((subgroupAdditivePointsEquiv J).trans e).toMultiplicativeRight⟩⟩)

variable {S : Scheme.{u}} {A : Over S} [GrpObj A] [IsCommMonObj A]
  (n : ℕ) (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
  (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S)
  (p : A ⟶ A) [IsMonHom p]
  [IsFinite (OppositeKernel.Construction.torsionBlock n p).hom] [Etale (OppositeKernel.Construction.torsionBlock n p).hom]
  {V : Type*} [AddGroup V] (e : V ≃+ Additive (Over.mk b ⟶ OppositeKernel.Construction.torsionBlock n p))

def geometricSupportedAdditiveChoiceEquiv :
    SubgroupFunctor.Construction.SupportedChoice A n M p (Over.mk b) ≃
      {J : AddSubgroup V // Nonempty (J ≃+ M)} :=
  ((BlockChoices.Construction.geometricSupportedChoiceEquiv n M K b p).trans typedSubgroupAdditiveEquiv).trans
    (TateChoices.Construction.typedAdditiveSubgroupEquiv e.symm)

theorem geometricSupportedAdditiveChoiceEquiv_membership
    (F : SubgroupFunctor.Construction.SupportedChoice A n M p (Over.mk b)) (x : V) :
    x ∈ (geometricSupportedAdditiveChoiceEquiv n M K b p e F).val ↔
      (e x).toMul ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈ F.val.subgroup.points (Over.mk b) (𝟙 _) := by
  change x ∈ (BlockChoices.Construction.geometricSupportedChoiceEquiv n M K b p F).val.toAddSubgroup.map
    e.symm.toAddMonoidHom ↔ _
  rw [AddSubgroup.mem_map_equiv]
  exact BlockChoices.Construction.geometricSupportedChoiceEquiv_membership n M K b p F (e x).toMul

def typedAdditiveTargetEquiv {G M N : Type*} [AddGroup G] [AddGroup M] [AddGroup N]
    (e : M ≃+ N) :
    {J : AddSubgroup G // Nonempty (J ≃+ M)} ≃
      {J : AddSubgroup G // Nonempty (J ≃+ N)} :=
  Equiv.subtypeEquivRight fun _ =>
    ⟨fun ⟨f⟩ => ⟨f.trans e⟩, fun ⟨f⟩ => ⟨f.trans e.symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction
