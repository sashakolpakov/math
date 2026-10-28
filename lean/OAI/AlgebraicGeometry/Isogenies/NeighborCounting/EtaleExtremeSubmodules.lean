import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.EtaleLineInclusion
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange

/-! # Etale Extreme Submodules -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleExtremeSubmodules

noncomputable section

/-! The zero and full etale submodules retain their literal constant
group carriers after arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

local instance extremeSubmodulePullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.EtaleLineInclusion
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable {S T : Scheme}

theorem etaleSubsingleton_points (G : Type) [Group G] [Subsingleton G]
    (U : Over S) (a : U ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) : a = 1 := by
  apply ((AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupPointIso S G).app (op U)).groupIsoToMulEquiv.injective
  apply LocallyConstant.ext
  intro x
  exact Subsingleton.elim _ _

theorem pulledEtaleSubsingleton_points (f : T ⟶ S) (G : Type) [Group G] [Subsingleton G]
    (U : Over T) (a : U ⟶ (Over.pullback f).obj (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G).X) : a = 1 := by
  let e := (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S G) U).symm
  apply e.injective
  exact (etaleSubsingleton_points G ((Over.map f).obj U) (e a)).trans e.map_one.symm

variable (f : T ⟶ S) (q : ℕ) [Fact q.Prime]

def geometricEtaleTopIso :
    (Over.pullback f).mapGrp.obj
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S (Multiplicative (⊤ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)))) ≅
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme T q :=
  (Over.pullback f).mapGrp.mapIso
    (AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso S (Submodule.topEquiv : (⊤ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) ≃ₗ[ZMod q]
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q).toAddEquiv.toMultiplicative) ≪≫ Geometric.EtaleLineInclusion.geometricEtalePlaneIso f q

theorem geometricEtaleTopIso_inclusion :
    (geometricEtaleTopIso f q).hom =
      (Over.pullback f).mapGrp.map (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap S
        (⊤ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)).subtype.toAddMonoidHom.toMultiplicative) ≫
          (Geometric.EtaleLineInclusion.geometricEtalePlaneIso f q).hom := rfl

theorem pulledEtaleBottom_points (U : Over T)
    (a : U ⟶ (Over.pullback f).obj
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S (Multiplicative (⊥ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)))).X) : a = 1 :=
  pulledEtaleSubsingleton_points f _ U a

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleExtremeSubmodules
