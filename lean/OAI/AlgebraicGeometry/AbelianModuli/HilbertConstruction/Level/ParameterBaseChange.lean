import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Parameters

/-! # Parameter Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Compatibility of the explicit change-of-level labels with geometric base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {S S' : Scheme.{u}} {G H : Type v} [Group G] [Group H]

/-- Base change of an isomorphism between constant group functors. -/
def Level.ParameterBaseChange.constantGroupIsoPullback (e : Constant.GroupMaps.constantGroupFunctor S G ≅ Constant.GroupMaps.constantGroupFunctor S H)
    (f : S' ⟶ S) : Constant.GroupMaps.constantGroupFunctor S' G ≅ Constant.GroupMaps.constantGroupFunctor S' H :=
  Functor.isoWhiskerLeft (Over.map f).op e

/-- The label isomorphisms pull back as locally constant functions on the base. -/
theorem Level.ParameterBaseChange.constantGroupIsoLabels_pullback [Finite G]
    (e : Constant.GroupMaps.constantGroupFunctor S G ≅ Constant.GroupMaps.constantGroupFunctor S H) (f : S' ⟶ S) :
    Constant.GroupIsomorphisms.constantGroupIsoLabels (Level.ParameterBaseChange.constantGroupIsoPullback e f) =
      (Constant.GroupIsomorphisms.constantGroupIsoLabels e).comap ⟨f, f.continuous⟩ := by
  apply LocallyConstant.ext
  intro s
  apply MulEquiv.ext
  intro g
  exact Constant.GroupMaps.constantGroupMap_apply e.hom ((Over.map f).obj (Over.mk (𝟙 S')))
    (LocallyConstant.const S' g) s

variable {g N : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

/-- Changing a level and then pulling back agrees with pulling back both levels. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.changeEquiv_pullback (base level : A.FullLevel N) (f : S' ⟶ S) :
    (base.pullback f).changeEquiv (level.pullback f) =
      Level.ParameterBaseChange.constantGroupIsoPullback (base.changeEquiv level) f := by
  apply Iso.ext
  apply NatTrans.ext
  funext T
  let e := (A.torsionBaseChangeIso f N).app T
  change (level.hom.app (.op ((Over.map f).obj T.unop)) ≫ e.inv) ≫
      (e.hom ≫ base.inv.app (.op ((Over.map f).obj T.unop))) =
    level.hom.app (.op ((Over.map f).obj T.unop)) ≫
      base.inv.app (.op ((Over.map f).obj T.unop))
  exact (Category.assoc _ _ _).trans
    (congrArg (fun a => level.hom.app (.op ((Over.map f).obj T.unop)) ≫ a)
      (e.inv_hom_id_assoc _))

/-- The locally constant parameters for a level change commute with arbitrary base change. -/
theorem Abelian.Schemes.AbelianScheme.FullLevel.labelsEquiv_pullback [NeZero N] (base level : A.FullLevel N) (f : S' ⟶ S) :
    (base.pullback f).labelsEquiv (level.pullback f) =
      (base.labelsEquiv level).comap ⟨f, f.continuous⟩ :=
  (congrArg Constant.GroupIsomorphisms.constantGroupIsoLabels (Abelian.Schemes.AbelianScheme.FullLevel.changeEquiv_pullback base level f)).trans
    (Level.ParameterBaseChange.constantGroupIsoLabels_pullback (base.changeEquiv level) f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
