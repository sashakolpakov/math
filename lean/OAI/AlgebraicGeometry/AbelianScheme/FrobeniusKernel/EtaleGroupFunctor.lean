import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups

/-! # Etale Group Functor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction

noncomputable section

/-! Native functoriality of finite constant group schemes, verified on
all test schemes through their original locally constant sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

variable (S : Scheme.{u}) {G H K : Type u} [Group G] [Group H] [Group K]

theorem etaleGroupHom_ext
    {a b : EtaleSubgroups.Construction.etaleGroupScheme S G ⟶ EtaleSubgroups.Construction.etaleGroupScheme S H}
    (h : ∀ (T : Over S) (t : T ⟶ (EtaleSubgroups.Construction.etaleGroupScheme S G).X) (x : T.left),
      LocallyConstant.toFun ((EtaleSubgroups.Construction.etaleGroupPointIso S H).hom.app (op T)
        (t ≫ a.hom.hom)) x =
      LocallyConstant.toFun ((EtaleSubgroups.Construction.etaleGroupPointIso S H).hom.app (op T)
        (t ≫ b.hom.hom)) x) : a = b := by
  apply yonedaGrp.map_injective
  apply NatTrans.ext
  funext T
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro t
  apply ((EtaleSubgroups.Construction.etaleGroupPointIso S H).app T).groupIsoToMulEquiv.injective
  exact LocallyConstant.ext (h T.unop t)

theorem etaleGroupMap_id : EtaleSubgroups.Construction.etaleGroupMap S (MonoidHom.id G) = 𝟙 _ := by
  apply etaleGroupHom_ext
  intro T t x
  exact EtaleSubgroups.Construction.etaleGroupMap_sections S (MonoidHom.id G) T t x

theorem etaleGroupMap_comp (f : G →* H) (g : H →* K) :
    EtaleSubgroups.Construction.etaleGroupMap S f ≫ EtaleSubgroups.Construction.etaleGroupMap S g = EtaleSubgroups.Construction.etaleGroupMap S (g.comp f) := by
  apply etaleGroupHom_ext
  intro T t x
  change LocallyConstant.toFun ((EtaleSubgroups.Construction.etaleGroupPointIso S K).hom.app (op T)
    (t ≫ (EtaleSubgroups.Construction.etaleGroupMap S f).hom.hom ≫ (EtaleSubgroups.Construction.etaleGroupMap S g).hom.hom)) x = _
  rw [← Category.assoc, EtaleSubgroups.Construction.etaleGroupMap_sections, EtaleSubgroups.Construction.etaleGroupMap_sections,
    EtaleSubgroups.Construction.etaleGroupMap_sections]
  rfl

/-- An isomorphism of the original labels induces an actual native
group-scheme isomorphism. -/
def etaleGroupIso (a : G ≃* H) : EtaleSubgroups.Construction.etaleGroupScheme S G ≅ EtaleSubgroups.Construction.etaleGroupScheme S H where
  hom := EtaleSubgroups.Construction.etaleGroupMap S a.toMonoidHom
  inv := EtaleSubgroups.Construction.etaleGroupMap S a.symm.toMonoidHom
  hom_inv_id := by
    rw [etaleGroupMap_comp]
    convert etaleGroupMap_id S using 1
    exact congrArg (EtaleSubgroups.Construction.etaleGroupMap S) (MonoidHom.ext a.symm_apply_apply)
  inv_hom_id := by
    rw [etaleGroupMap_comp]
    convert etaleGroupMap_id S using 1
    exact congrArg (EtaleSubgroups.Construction.etaleGroupMap S) (MonoidHom.ext a.apply_symm_apply)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction
