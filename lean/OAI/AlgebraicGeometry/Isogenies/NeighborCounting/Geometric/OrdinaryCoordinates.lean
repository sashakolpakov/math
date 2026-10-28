import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.CoordinateSpecialKernels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MultiplicativeBlockBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveEtaleTransport

/-! # Ordinary Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The actual integral coordinate model induces an ordinary product
on the original geometric special fiber. Its line permutation relative
to any independently given ordinary chart is then constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MultiplicativeBlockBaseChange
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricIdentityIso :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj C.identity ≅
      AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 1 :=
  (AbelianScheme.FrobeniusKernel.GroupPullbackComposition.Construction.groupPullbackCompIso (Spec.map (CommRingCat.ofHom ρ.symm.toRingHom)) (Lifts.closedBase R)).app C.identity ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom ρ.symm.toRingHom))).mapGrp.mapIso C.special ≪≫
      MultiplicativeBlockBaseChange.multiplicativeBlockRingHomBaseChangeIso (IsLocalRing.ResidueField R) (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
        ρ.symm.toRingHom q 1 1

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricEtaleIso :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))) ≅
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q :=
  EtaleBlockBaseChange.etaleBlockBaseChangeIso (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))
    (Multiplicative (Fin 2 → ZMod q)) ≪≫
      AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) MulEquiv.ulift.symm

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricSplitting :
    AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj A) :=
  (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.mapIso C.split.symm ≪≫
    (Functor.Monoidal.μIso (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp
      C.identity (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q)))).symm ≪≫
      tensorIso (C.geometricIdentityIso R L q A ρ) (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricEtaleIso R q ρ)

variable {B : Grp (Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))}
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q B)
  (a : (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj A ≅ B)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricLineEquiv : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q :=
  AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineEquiv (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricLineIso (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q J ≅
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q
        (C.geometricLineEquiv R L q A ρ e a J) :=
  AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineIso (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a J

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricLineIso_inclusion (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (C.geometricLineIso R L q A ρ e a J).hom ≫
      AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e (C.geometricLineEquiv R L q A ρ e a J) =
      AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) J ≫ a.hom :=
  AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineIso_inclusion (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a J

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
