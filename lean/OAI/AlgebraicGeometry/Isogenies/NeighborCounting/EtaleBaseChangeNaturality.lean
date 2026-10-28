import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleBlockBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange

/-! # Etale Base Change Naturality -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleBaseChangeNaturality.Block

noncomputable section

/-! The actual constant-group base-change isomorphism respects the
original homomorphisms of labels on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange.Construction
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {S T : Scheme} (f : T ⟶ S) {G H : Type} [Group G] [Group H]

theorem etaleBlockBaseChangeIso_sections (U : Over T)
    (a : U ⟶ ((Over.pullback f).mapGrp.obj (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G)).X) :
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso T G).hom.app (op U)
        (a ≫ (EtaleBlockBaseChange.etaleBlockBaseChangeIso f G).hom.hom.hom) =
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).hom.app (op ((Over.map f).obj U))
        ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G) U).symm a) := by
  have h := (yonedaGrpFullyFaithful (C := Over T)).map_preimage
    (((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G)).symm ≪≫
      Functor.isoWhiskerLeft (Over.map f).op (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G) ≪≫
        EtaleBlockBaseChange.constantGroupFunctorBaseChangeIso f G ≪≫ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso T G).symm).hom)
  have hc := congrArg (fun α => α ≫ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso T G).hom) h
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] at hc
  exact congrArg (fun α => (α.app (op U)).hom a) hc

theorem etaleBlockBaseChangeIso_naturality (k : G →* H) :
    (Over.pullback f).mapGrp.map (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap S k) ≫
        (EtaleBlockBaseChange.etaleBlockBaseChangeIso f H).hom =
      (EtaleBlockBaseChange.etaleBlockBaseChangeIso f G).hom ≫ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap T k := by
  apply yonedaGrp.map_injective
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro a
  change U.unop ⟶ (Over.pullback f).obj (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X at a
  apply ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso T H).app U).groupIsoToMulEquiv.injective
  apply LocallyConstant.ext
  intro x
  have hl := etaleBlockBaseChangeIso_sections f U.unop
    (a ≫ (Over.pullback f).map (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap S k).hom.hom)
  have hr := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap_sections T k U.unop
    (a ≫ (EtaleBlockBaseChange.etaleBlockBaseChangeIso f G).hom.hom.hom) x
  have hg := etaleBlockBaseChangeIso_sections f U.unop a
  have hn := (Over.mapPullbackAdj f).homEquiv_naturality_right_symm a
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap S k).hom.hom
  change (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S H) U.unop).symm
      (a ≫ (Over.pullback f).map (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap S k).hom.hom) =
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G) U.unop).symm a ≫
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap S k).hom.hom at hn
  exact (congrArg (fun c : LocallyConstant U.unop.left H => c x) hl).trans
    ((congrArg (fun t => LocallyConstant.toFun ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S H).hom.app
      (op ((Over.map f).obj U.unop)) t) x) hn).trans
      ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap_sections S k ((Over.map f).obj U.unop)
        ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G) U.unop).symm a) x).trans
          ((congrArg (fun c : LocallyConstant U.unop.left G => k (c x)) hg).symm.trans hr.symm)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleBaseChangeNaturality.Block
