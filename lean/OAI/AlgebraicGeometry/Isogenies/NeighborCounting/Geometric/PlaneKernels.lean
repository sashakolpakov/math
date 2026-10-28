import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleExtremeSubmodules
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.GraphLineKernel

/-! # Plane Kernels -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The full etale special kernel and the full mixed special kernel
retain their original carriers and inclusions in the geometric q-block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleExtremeSubmodules

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricGraphPlane_inclusion :
    (EtaleExtremeSubmodules.geometricEtaleTopIso (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) q).hom.hom.hom ≫
      (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ)).hom.hom =
      (C.geometricSpecialKernel R L q A ρ ⊤ false).inclusion := by
  let f := Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)
  let F := (Over.pullback f).mapGrp
  let k := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap (Spec (.of R))
    (⊤ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)).subtype.toAddMonoidHom.toMultiplicative
  let p := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ)
  have hi := EtaleExtremeSubmodules.geometricEtaleTopIso_inclusion f q
  have hp := C.geometricEtalePlane_inclusion R L q A ρ
  have h : (EtaleExtremeSubmodules.geometricEtaleTopIso f q).hom ≫ p =
      F.map (k ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion C.identity
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))) ≫ C.split.hom) := by
    rw [hi, Category.assoc]
    change F.map k ≫ (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricEtaleIso R q ρ).hom ≫ p = _
    rw [hp, ← F.map_comp]
  have hz : QuotientGraphs.graphKernel C.split.hom.hom.hom k.hom.hom 1 =
      (k ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion C.identity
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))) ≫ C.split.hom).hom.hom := by
    change lift (1 : _ ⟶ C.identity.X) k.hom.hom ≫ C.split.hom.hom.hom =
      k.hom.hom ≫ lift (1 : _ ⟶ C.identity.X) (𝟙 _) ≫ C.split.hom.hom.hom
    rw [← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id]
  exact (congrArg (fun u => u.hom.hom) h).trans
    (congrArg (fun u => (Over.pullback f).map u) hz.symm)

variable {B : Grp (Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))}
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q B)
  (a : (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj A ≅ B)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricGraphIndependentPlaneIso :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R))
          (Multiplicative (⊤ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)))) ≅
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q :=
  EtaleExtremeSubmodules.geometricEtaleTopIso (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) q ≪≫
    AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.activeEtaleIso (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricGraphIndependentPlane_inclusion :
    (C.geometricGraphIndependentPlaneIso R L q A ρ e a).hom.hom.hom ≫
      (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e).hom.hom =
      (C.geometricSpecialKernel R L q A ρ ⊤ false).inclusion ≫ a.hom.hom.hom := by
  let u := (EtaleExtremeSubmodules.geometricEtaleTopIso (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) q).hom.hom.hom
  let v := (AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.activeEtaleIso (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a).hom.hom.hom
  let k := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ)).hom.hom
  let h := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e).hom.hom
  have hv : v ≫ h = k ≫ a.hom.hom.hom :=
    congrArg (fun f => f.hom.hom) (AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.activeEtaleMap_inclusion
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a.hom)
  have hu : u ≫ k = (C.geometricSpecialKernel R L q A ρ ⊤ false).inclusion :=
    C.geometricGraphPlane_inclusion R L q A ρ
  exact (Category.assoc u v h).trans ((congrArg (fun f => u ≫ f) hv).trans
    ((Category.assoc u k a.hom.hom.hom).symm.trans (congrArg (fun f => f ≫ a.hom.hom.hom) hu)))

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricMixedTopIso :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj
        (C.identity ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R))
          (Multiplicative (⊤ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)))) ≅
      (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj A :=
  (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.mapIso
    (tensorIso (Iso.refl C.identity) (AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso (Spec (.of R))
      (Submodule.topEquiv : (⊤ : Submodule (ZMod q) (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) ≃ₗ[ZMod q]
        AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q).toAddEquiv.toMultiplicative) ≪≫ C.split)

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricMixedTopIso_inclusion :
    (C.geometricMixedTopIso R L q A ρ).hom.hom.hom =
      (C.geometricSpecialKernel R L q A ρ ⊤ true).inclusion := rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
