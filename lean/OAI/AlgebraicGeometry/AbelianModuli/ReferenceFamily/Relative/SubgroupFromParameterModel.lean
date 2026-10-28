import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.SubgroupFromParameter

/-! # Subgroup From Parameter Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.SubgroupFromParameterModel

noncomputable section

/-! Recovering a relative subgroup from the parameter keeps its
original finite locally free carrier and its actual inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) (P : Over S)
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup ((Over.pullback P.hom).obj G.X) (Over.mk (𝟙 P.left)))
    (R : F.Model)

def parameterModelOriginalGroupMap : (Over.map P.hom).obj R.carrier ⟶ G.X :=
  (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G R.carrier).symm R.toGroup

theorem parameterModelOriginalGroupMap_left :
    (parameterModelOriginalGroupMap G P F R).left =
      R.toGroup.left ≫ pullback.fst G.X.hom P.hom := rfl

def relativeSubgroupFromParameterModel : (SubgroupFromParameter.relativeSubgroupFromParameter G P F).Model where
  carrier := (Over.map P.hom).obj R.carrier
  toBase := AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P R.carrier
  toGroup := parameterModelOriginalGroupMap G P F R
  finite := by
    change IsFinite R.carrier.hom
    have hb := congrArg Over.Hom.left (SubgroupFromParameter.terminalParameterPoint_unique R.carrier R.toBase)
    change R.carrier.hom = R.toBase.left at hb
    rw [hb]
    exact R.finite
  flat := by
    change Flat R.carrier.hom
    have hb := congrArg Over.Hom.left (SubgroupFromParameter.terminalParameterPoint_unique R.carrier R.toBase)
    change R.carrier.hom = R.toBase.left at hb
    rw [hb]
    exact R.flat
  finitePresentation := by
    change LocallyOfFinitePresentation R.carrier.hom
    have hb := congrArg Over.Hom.left (SubgroupFromParameter.terminalParameterPoint_unique R.carrier R.toBase)
    change R.carrier.hom = R.toBase.left at hb
    rw [hb]
    exact R.finitePresentation
  jointly_monic X a b hb hg := by
    let X' : Over P.left := Over.mk (a.left ≫ R.carrier.hom)
    let a' : X' ⟶ R.carrier := Over.homMk a.left rfl
    let b' : X' ⟶ R.carrier := Over.homMk b.left (congrArg Over.Hom.left hb).symm
    have he : a' ≫ R.toGroup = b' ≫ R.toGroup := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · have h := congrArg Over.Hom.left hg
        change a.left ≫ (R.toGroup.left ≫ pullback.fst G.X.hom P.hom) =
          b.left ≫ (R.toGroup.left ≫ pullback.fst G.X.hom P.hom) at h
        exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
      · exact (a' ≫ R.toGroup).w.trans (b' ≫ R.toGroup).w.symm
    have hab : a' = b' := R.jointly_monic X' a' b'
      ((SubgroupFromParameter.terminalParameterPoint_unique X' (a' ≫ R.toBase)).symm.trans
        (SubgroupFromParameter.terminalParameterPoint_unique X' (b' ≫ R.toBase))) he
    apply Over.OverMorphism.ext
    exact congrArg (fun k : X' ⟶ R.carrier => k.left) hab
  points_iff X t a := by
    change ParameterPointTransport.parameterPointMulEquiv G P X t a ∈
      F.points (Over.mk t.left) (SubgroupFromParameter.terminalParameterPoint (Over.mk t.left)) ↔ _
    rw [R.points_iff]
    constructor
    · rintro ⟨z, _, hz⟩
      let r : X ⟶ (Over.map P.hom).obj R.carrier := Over.homMk z.left (by
        change z.left ≫ (R.carrier.hom ≫ P.hom) = X.hom
        rw [← Category.assoc, z.w]
        exact t.w)
      refine ⟨r, Over.OverMorphism.ext z.w, ?_⟩
      apply Over.OverMorphism.ext
      have h := congrArg (fun k : Over.mk t.left ⟶ (Over.pullback P.hom).obj G.X =>
        k.left ≫ pullback.fst G.X.hom P.hom) hz
      change (z.left ≫ R.toGroup.left) ≫ pullback.fst G.X.hom P.hom = _ at h
      change z.left ≫ (R.toGroup.left ≫ pullback.fst G.X.hom P.hom) = a.left
      exact (Category.assoc _ _ _).symm.trans
        (h.trans (ParameterPointTransport.parameterPointMulEquiv_fst G P X t a))
    · rintro ⟨r, hrb, hrg⟩
      let z : Over.mk t.left ⟶ R.carrier := Over.homMk r.left (congrArg Over.Hom.left hrb)
      refine ⟨z, (SubgroupFromParameter.terminalParameterPoint_unique _ (z ≫ R.toBase)).symm, ?_⟩
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · have h := congrArg Over.Hom.left hrg
        change r.left ≫ (R.toGroup.left ≫ pullback.fst G.X.hom P.hom) = a.left at h
        exact (Category.assoc _ _ _).trans
          (h.trans (ParameterPointTransport.parameterPointMulEquiv_fst G P X t a).symm)
      · exact (z ≫ R.toGroup).w.trans (ParameterPointTransport.parameterPointMulEquiv G P X t a).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.SubgroupFromParameterModel
