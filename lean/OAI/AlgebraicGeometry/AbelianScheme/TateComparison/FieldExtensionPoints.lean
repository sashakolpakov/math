import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Splitting
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.SubgroupChoices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor

/-! # Field Extension Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldExtensionPoints

noncomputable section

/-! Actual finite étale group points are unchanged by extending a
separably closed field. The equivalence is precomposition by the given
field morphism, so it retains all group maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {K k : Type} [Field K] [Field k]
  (b : Spec (.of k) ⟶ Spec (.of K))

def fieldTestMap : Over.mk b ⟶ Over.mk (𝟙 (Spec (.of K))) :=
  Over.homMk b (Category.comp_id b)

def fieldPointMap (H : Over (Spec (.of K))) [GrpObj H] :
    (Over.mk (𝟙 (Spec (.of K))) ⟶ H) →* (Over.mk b ⟶ H) where
  toFun p := fieldTestMap b ≫ p
  map_one' := MonObj.comp_one _
  map_mul' p r := MonObj.comp_mul _ p r

theorem fieldPointMap_injective (H : Over (Spec (.of K))) [GrpObj H] :
    Function.Injective (fieldPointMap b H) := by
  have : Epi (fieldTestMap b).left := IsogenyQuotient.Geometric.SubgroupChoices.Construction.field_scheme_morphism_epi b
  have : Epi (fieldTestMap b) := Over.epi_of_epi_left _
  exact fun _ _ h => (cancel_epi (fieldTestMap b)).mp h

theorem finiteEtale_fieldPointMap_surjective [IsSepClosed K]
    (H : Over (Spec (.of K))) [GrpObj H] [IsFinite H.hom] [Etale H.hom] :
    Function.Surjective (fieldPointMap b H) := by
  obtain ⟨G, hG, hfin, ⟨e⟩⟩ := AbelianModuli.ReferenceFamily.Geometric.Splitting.GeometricSplitting.exists_constant_groupIso H
  intro p
  let c : LocallyConstant (Spec (.of k)) G := e.inv.app (.op (Over.mk b)) p
  let c₀ : LocallyConstant (Spec (.of K)) G := LocallyConstant.const _ (c default)
  refine ⟨e.hom.app (.op (Over.mk (𝟙 (Spec (.of K))))) c₀, ?_⟩
  have hn := ConcreteCategory.congr_hom (e.hom.naturality (fieldTestMap b).op) c₀
  have hc : (AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor (Spec (.of K)) G).map
      (fieldTestMap b).op c₀ = c := by
    apply LocallyConstant.ext
    intro z
    exact congrArg c (Subsingleton.elim _ _)
  change e.hom.app (.op (Over.mk b))
      ((AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor (Spec (.of K)) G).map
        (fieldTestMap b).op c₀) = fieldPointMap b H
          (e.hom.app (.op (Over.mk (𝟙 (Spec (.of K))))) c₀) at hn
  rw [hc] at hn
  exact hn.symm.trans (ConcreteCategory.congr_hom (e.inv_hom_id_app (.op (Over.mk b))) p)

def finiteEtale_fieldPointEquiv [IsSepClosed K]
    (H : Over (Spec (.of K))) [GrpObj H] [IsFinite H.hom] [Etale H.hom] :
    (Over.mk (𝟙 (Spec (.of K))) ⟶ H) ≃* (Over.mk b ⟶ H) :=
  MulEquiv.ofBijective (fieldPointMap b H)
    ⟨fieldPointMap_injective b H, finiteEtale_fieldPointMap_surjective b H⟩

theorem fieldPointMap_natural
    {H J : Over (Spec (.of K))} [GrpObj H] [GrpObj J]
    (f : H ⟶ J) (p : Over.mk (𝟙 (Spec (.of K))) ⟶ H) :
    fieldPointMap b J (p ≫ f) = fieldPointMap b H p ≫ f :=
  (Category.assoc (fieldTestMap b) p f).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FieldExtensionPoints
