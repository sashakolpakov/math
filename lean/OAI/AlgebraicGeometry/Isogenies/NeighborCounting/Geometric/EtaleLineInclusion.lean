import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.OrdinaryCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleBaseChangeNaturality

/-! # Etale Line Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.EtaleLineInclusion

noncomputable section

/-! The actual specialized integral line labels give the chosen native
etale line, with their original inclusion in the full etale plane. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EtaleBaseChangeNaturality.Block

local instance geometricEtaleLinePullbackMonoidal {X Y : Scheme} (f : X ⟶ Y) :
    (Over.pullback f).Monoidal := Over.instBraidedPullback.toMonoidal

variable {S T : Scheme} (f : T ⟶ S) (q : ℕ) [Fact q.Prime]

def geometricEtaleLineIso (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (Over.pullback f).mapGrp.obj (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S (Multiplicative J.val)) ≅
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme T q J :=
  EtaleBlockBaseChange.etaleBlockBaseChangeIso f (Multiplicative J.val) ≪≫
    AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso T MulEquiv.ulift.symm

def geometricEtalePlaneIso :
    (Over.pullback f).mapGrp.obj (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme S (Multiplicative (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q))) ≅
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme T q :=
  EtaleBlockBaseChange.etaleBlockBaseChangeIso f (Multiplicative (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)) ≪≫
    AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso T MulEquiv.ulift.symm

theorem etaleLine_ulift_inclusion (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso T (MulEquiv.ulift.symm : Multiplicative J.val ≃* ULift (Multiplicative J.val))).hom ≫
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding T q J =
    AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap T J.val.subtype.toAddMonoidHom.toMultiplicative ≫
      (AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso T (MulEquiv.ulift.symm :
        Multiplicative (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q) ≃* ULift (Multiplicative (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)))).hom := by
  change AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap T _ ≫ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap T _ = AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap T _ ≫ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap T _
  rw [AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupMap_comp, AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupMap_comp]
  apply congrArg (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap T)
  exact MonoidHom.ext (fun _ => rfl)

theorem geometricEtaleLineIso_inclusion (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (geometricEtaleLineIso f q J).hom ≫ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding T q J =
      (Over.pullback f).mapGrp.map
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap S J.val.subtype.toAddMonoidHom.toMultiplicative) ≫
          (geometricEtalePlaneIso f q).hom := by
  let u := (EtaleBlockBaseChange.etaleBlockBaseChangeIso f (Multiplicative J.val)).hom
  let v := (AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso T (MulEquiv.ulift.symm :
    Multiplicative J.val ≃* ULift (Multiplicative J.val))).hom
  let i := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding T q J
  let k := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap T J.val.subtype.toAddMonoidHom.toMultiplicative
  let w := (AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso T (MulEquiv.ulift.symm : Multiplicative (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q) ≃*
    ULift (Multiplicative (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q)))).hom
  let z := (Over.pullback f).mapGrp.map
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap S J.val.subtype.toAddMonoidHom.toMultiplicative)
  let b := (EtaleBlockBaseChange.etaleBlockBaseChangeIso f (Multiplicative (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtalePlane q))).hom
  have hi : v ≫ i = k ≫ w := etaleLine_ulift_inclusion q J
  have hn : z ≫ b = u ≫ k :=
    EtaleBaseChangeNaturality.Block.etaleBlockBaseChangeIso_naturality f J.val.subtype.toAddMonoidHom.toMultiplicative
  exact (Category.assoc u v i).trans ((congrArg (fun h => u ≫ h) hi).trans
    ((Category.assoc u k w).symm.trans ((congrArg (fun h => h ≫ w) hn.symm).trans
      (Category.assoc z b w))))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.EtaleLineInclusion
