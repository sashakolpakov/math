import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps

/-! # Group Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms

noncomputable section

/-! Isomorphisms of finite constant groups, including disconnected bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Topology

universe u v

variable {S : Scheme.{u}} {G H K : Type v} [Group G] [Group H] [Group K]

@[simp]
theorem constantGroupMapAt_id (s : S) :
    GroupMaps.constantGroupMapAt (𝟙 (GroupMaps.constantGroupFunctor S G)) s = MonoidHom.id G := rfl

/-- Composition of natural maps agrees with composition of their pointwise label maps. -/
theorem constantGroupMapAt_comp
    (α : GroupMaps.constantGroupFunctor S G ⟶ GroupMaps.constantGroupFunctor S H)
    (β : GroupMaps.constantGroupFunctor S H ⟶ GroupMaps.constantGroupFunctor S K) (s : S) :
    GroupMaps.constantGroupMapAt (α ≫ β) s = (GroupMaps.constantGroupMapAt β s).comp (GroupMaps.constantGroupMapAt α s) := by
  apply MonoidHom.ext
  intro g
  exact GroupMaps.constantGroupMap_apply β (Over.mk (𝟙 S))
    (α.app (.op (Over.mk (𝟙 S))) (LocallyConstant.const S g)) s

@[simp]
theorem constantGroupMapAt_ofLabels (a : LocallyConstant S (G →* H)) (s : S) :
    GroupMaps.constantGroupMapAt (GroupMaps.constantGroupMapOfLabels a) s = a s := rfl

/-- A natural isomorphism gives an isomorphism of label groups at every base point. -/
def constantGroupIsoAt (e : GroupMaps.constantGroupFunctor S G ≅ GroupMaps.constantGroupFunctor S H) (s : S) :
    G ≃* H where
  toFun := GroupMaps.constantGroupMapAt e.hom s
  invFun := GroupMaps.constantGroupMapAt e.inv s
  left_inv g := congrArg (fun a : G →* G => a g)
    ((constantGroupMapAt_comp e.hom e.inv s).symm.trans
      ((congrArg (fun a => GroupMaps.constantGroupMapAt a s) e.hom_inv_id).trans (constantGroupMapAt_id s)))
  right_inv h := congrArg (fun a : H →* H => a h)
    ((constantGroupMapAt_comp e.inv e.hom s).symm.trans
      ((congrArg (fun a => GroupMaps.constantGroupMapAt a s) e.inv_hom_id).trans (constantGroupMapAt_id s)))
  map_mul' := (GroupMaps.constantGroupMapAt e.hom s).map_mul

/-- With finite labels, the isomorphism of label groups is locally constant on the base. -/
def constantGroupIsoLabels [Finite G]
    (e : GroupMaps.constantGroupFunctor S G ≅ GroupMaps.constantGroupFunctor S H) :
    LocallyConstant S (G ≃* H) where
  toFun := constantGroupIsoAt e
  isLocallyConstant := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro s
    exact ((GroupMaps.constantGroupMapLabels e.hom).isLocallyConstant.eventually_eq s).mono
      (fun _ h => MulEquiv.ext (fun g => congrArg (fun a : G →* H => a g) h))

/-- A locally constant family of label isomorphisms gives a natural group isomorphism. -/
def constantGroupIsoOfLabels (a : LocallyConstant S (G ≃* H)) :
    GroupMaps.constantGroupFunctor S G ≅ GroupMaps.constantGroupFunctor S H where
  hom := GroupMaps.constantGroupMapOfLabels (a.map MulEquiv.toMonoidHom)
  inv := GroupMaps.constantGroupMapOfLabels (a.map (fun e => e.symm.toMonoidHom))
  hom_inv_id := by
    apply GroupMaps.constantGroupMap_ext
    intro s
    apply MonoidHom.ext
    intro g
    exact (congrArg (fun b : G →* G => b g) (constantGroupMapAt_comp _ _ s)).trans
      ((a s).symm_apply_apply g)
  inv_hom_id := by
    apply GroupMaps.constantGroupMap_ext
    intro s
    apply MonoidHom.ext
    intro h
    exact (congrArg (fun b : H →* H => b h) (constantGroupMapAt_comp _ _ s)).trans
      ((a s).apply_symm_apply h)

/-- The full isomorphism set of two constant group functors is the set of locally constant
families of isomorphisms of their finite label groups. -/
def constantGroupIsoEquiv [Finite G] :
    (GroupMaps.constantGroupFunctor S G ≅ GroupMaps.constantGroupFunctor S H) ≃ LocallyConstant S (G ≃* H) where
  toFun := constantGroupIsoLabels
  invFun := constantGroupIsoOfLabels
  left_inv e := by
    apply Iso.ext
    apply GroupMaps.constantGroupMap_ext
    intro s
    apply MonoidHom.ext
    intro g
    rfl
  right_inv a := by
    apply LocallyConstant.ext
    intro s
    apply MulEquiv.ext
    intro g
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms
