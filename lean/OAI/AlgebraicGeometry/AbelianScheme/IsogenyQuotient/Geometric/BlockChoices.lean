import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TorsionChoices
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SupportedBlockChoices

/-! # Block Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.BlockChoices.Construction

noncomputable section

/-!
Geometric points of supported subgroup choices classify unmarked
subgroups of the native block's actual points. The membership formula
retains the original subgroup and its inclusion into the abelian scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

def multiplicativeSubgroupEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Subgroup G ≃ Subgroup H where
  toFun F := F.map e.toMonoidHom
  invFun F := F.map e.symm.toMonoidHom
  left_inv F := (Subgroup.map_symm_eq_iff_map_eq F (e := e)).mpr rfl
  right_inv F := (Subgroup.map_symm_eq_iff_map_eq F (e := e.symm)).mpr rfl

def typedMultiplicativeSubgroupEquiv {G H M : Type*} [Group G] [Group H] [Group M]
    (e : G ≃* H) :
    {F : Subgroup G // Nonempty (F ≃* M)} ≃
      {F : Subgroup H // Nonempty (F ≃* M)} :=
  (multiplicativeSubgroupEquiv e).subtypeEquiv (fun F => by
    let eF := e.subgroupMap F
    exact ⟨fun ⟨f⟩ => ⟨eF.symm.trans f⟩, fun ⟨f⟩ => ⟨eF.trans f⟩⟩)

variable {S : Scheme.{u}} (H : Over S) [GrpObj H] [IsCommMonObj H]
  (n : ℕ) (hH : (𝟙 H) ^ n = 1)

def torsionOfKilledIso : TorsionQuotient.SubgroupFunctor.torsionScheme H n ≅ H where
  hom := TorsionQuotient.SubgroupFunctor.torsionι H n
  inv := TorsionQuotient.SubgroupFunctor.torsionLift n (𝟙 H) hH
  hom_inv_id := by
    apply (cancel_mono (TorsionQuotient.SubgroupFunctor.torsionι H n)).mp
    rw [Category.assoc, TorsionQuotient.SubgroupFunctor.torsionLift_ι, Category.comp_id, Category.id_comp]
  inv_hom_id := TorsionQuotient.SubgroupFunctor.torsionLift_ι n (𝟙 H) hH

def torsionOfKilledPointsEquiv (X : Over S) : (X ⟶ TorsionQuotient.SubgroupFunctor.torsionScheme H n) ≃* (X ⟶ H) where
  toFun x := x ≫ (torsionOfKilledIso H n hH).hom
  invFun x := x ≫ (torsionOfKilledIso H n hH).inv
  left_inv x := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv x := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  map_mul' x y := MonObj.mul_comp x y (TorsionQuotient.SubgroupFunctor.torsionι H n)

include hH in
theorem torsionOfKilled_finite_etale [IsFinite H.hom] [Etale H.hom] :
    IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme H n).hom ∧ Etale (TorsionQuotient.SubgroupFunctor.torsionScheme H n).hom := by
  have : IsIso (torsionOfKilledIso H n hH).hom.left :=
    (Over.forget S).map_isIso (torsionOfKilledIso H n hH).hom
  rw [← (torsionOfKilledIso H n hH).hom.w]
  exact ⟨inferInstance, inferInstance⟩

variable (M : Type u) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
  [IsFinite H.hom] [Etale H.hom]
  (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S)

def geometricKilledChoiceEquiv :
    TorsionQuotient.SubgroupFunctor.SubgroupChoice H n M (Over.mk b) ≃
      {J : Subgroup (Over.mk b ⟶ H) // Nonempty (J ≃* Multiplicative M)} := by
  have := (torsionOfKilled_finite_etale H n hH).1
  have := (torsionOfKilled_finite_etale H n hH).2
  exact (TorsionChoices.Construction.geometricTorsionChoiceEquiv H n M K b).trans
    (typedMultiplicativeSubgroupEquiv (torsionOfKilledPointsEquiv H n hH (Over.mk b)))

theorem geometricKilledChoiceEquiv_points (F : TorsionQuotient.SubgroupFunctor.SubgroupChoice H n M (Over.mk b)) :
    (geometricKilledChoiceEquiv H n hH M K b F).val = F.subgroup.points (Over.mk b) (𝟙 _) := by
  have := (torsionOfKilled_finite_etale H n hH).1
  have := (torsionOfKilled_finite_etale H n hH).2
  change ((TorsionChoices.Construction.geometricTorsionChoiceEquiv H n M K b F).val.map
    (torsionOfKilledPointsEquiv H n hH (Over.mk b)).toMonoidHom) = _
  rw [TorsionChoices.Construction.geometricTorsionChoiceEquiv_points]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    let y := TorsionQuotient.SubgroupFunctor.torsionLift n x (F.killed _ (𝟙 _) x hx)
    have hy : y ≫ TorsionQuotient.SubgroupFunctor.torsionι H n = x := TorsionQuotient.SubgroupFunctor.torsionLift_ι _ _ _
    refine ⟨y, ?_, hy⟩
    change y ≫ TorsionQuotient.SubgroupFunctor.torsionι H n ∈ F.subgroup.points (Over.mk b) (𝟙 _)
    rwa [hy]

variable {A : Over S} [GrpObj A] [IsCommMonObj A] (p : A ⟶ A) [IsMonHom p]
  [IsFinite (OppositeKernel.Construction.torsionBlock n p).hom] [Etale (OppositeKernel.Construction.torsionBlock n p).hom]

def geometricSupportedChoiceEquiv :
    SubgroupFunctor.Construction.SupportedChoice A n M p (Over.mk b) ≃
      {J : Subgroup (Over.mk b ⟶ OppositeKernel.Construction.torsionBlock n p) // Nonempty (J ≃* Multiplicative M)} :=
  (SupportedBlockChoices.Construction.supportedChoiceBlockEquiv n p M).trans
    (geometricKilledChoiceEquiv (OppositeKernel.Construction.torsionBlock n p) n (SupportedBlockChoices.Construction.torsionBlock_identity_killed n p) M K b)

theorem geometricSupportedChoiceEquiv_points (F : SubgroupFunctor.Construction.SupportedChoice A n M p (Over.mk b)) :
    (geometricSupportedChoiceEquiv n M K b p F).val =
      (SubgroupTransport.Construction.relativeSubgroupPullback (OppositeKernel.Construction.torsionBlockInclusion n p) F.val.subgroup).points
        (Over.mk b) (𝟙 _) :=
  geometricKilledChoiceEquiv_points (OppositeKernel.Construction.torsionBlock n p) n (SupportedBlockChoices.Construction.torsionBlock_identity_killed n p)
    M K b (SupportedBlockChoices.Construction.supportedChoiceToBlock n p M F)

theorem geometricSupportedChoiceEquiv_membership
    (F : SubgroupFunctor.Construction.SupportedChoice A n M p (Over.mk b)) (x : Over.mk b ⟶ OppositeKernel.Construction.torsionBlock n p) :
    x ∈ (geometricSupportedChoiceEquiv n M K b p F).val ↔
      x ≫ OppositeKernel.Construction.torsionBlockInclusion n p ∈ F.val.subgroup.points (Over.mk b) (𝟙 _) := by
  rw [geometricSupportedChoiceEquiv_points]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.BlockChoices.Construction
