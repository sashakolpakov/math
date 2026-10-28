import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.EtaleLineInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PulledOrdinaryFactorInclusion

/-! # Mixed Line Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The actual mixed special kernel is the product of the native
multiplicative factor and the transported etale line, including its map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.EtaleLineInclusion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PulledOrdinaryFactorInclusion.TensorSubgroup

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricMixedLineSourceIso (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj
        (C.identity ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative J.val)) ≅
      AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 1 ⊗
        AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q J :=
  (Functor.Monoidal.μIso (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp
    C.identity (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative J.val))).symm ≪≫
      tensorIso (C.geometricIdentityIso R L q A ρ)
        (Geometric.EtaleLineInclusion.geometricEtaleLineIso (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) q J)

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricMixedLine_inclusion (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (C.geometricMixedLineSourceIso R L q A ρ J).hom.hom.hom ≫
      (ActiveMixedLineTransport.chosenActiveMixedLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) J).hom.hom =
      (C.geometricSpecialKernel R L q A ρ J.val true).inclusion := by
  have h := PulledOrdinaryFactorInclusion.TensorSubgroup.pulledTensorSubgroup_inclusion (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) C.split
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap (Spec (.of R)) J.val.subtype.toAddMonoidHom.toMultiplicative)
    (C.geometricIdentityIso R L q A ρ) (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricEtaleIso R q ρ)
    (Geometric.EtaleLineInclusion.geometricEtaleLineIso (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) q J)
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q J)
    (Geometric.EtaleLineInclusion.geometricEtaleLineIso_inclusion (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) q J)
  exact congrArg (fun f => f.hom.hom) h

variable {B : Grp (Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))}
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q B)
  (a : (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj A ≅ B)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricMixedIndependentLineIso (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj
        (C.identity ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative J.val)) ≅
      AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 1 ⊗
        AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q
          (C.geometricLineEquiv R L q A ρ e a J) :=
  C.geometricMixedLineSourceIso R L q A ρ J ≪≫
    ActiveMixedLineTransport.chosenActiveMixedLineIso (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a J

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricMixedIndependentLine_inclusion (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (C.geometricMixedIndependentLineIso R L q A ρ e a J).hom.hom.hom ≫
      (ActiveMixedLineTransport.chosenActiveMixedLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e (C.geometricLineEquiv R L q A ρ e a J)).hom.hom =
      (C.geometricSpecialKernel R L q A ρ J.val true).inclusion ≫ a.hom.hom.hom := by
  let u := (C.geometricMixedLineSourceIso R L q A ρ J).hom.hom.hom
  let v := (ActiveMixedLineTransport.chosenActiveMixedLineIso (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q
    (C.geometricSplitting R L q A ρ) e a J).hom.hom.hom
  let k := (ActiveMixedLineTransport.chosenActiveMixedLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q
    (C.geometricSplitting R L q A ρ) J).hom.hom
  let h := (ActiveMixedLineTransport.chosenActiveMixedLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e
    (C.geometricLineEquiv R L q A ρ e a J)).hom.hom
  have hv : v ≫ h = k ≫ a.hom.hom.hom :=
    congrArg (fun f => f.hom.hom) (ActiveMixedLineTransport.chosenActiveMixedLineIso_inclusion
      (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) e a J)
  have hu : u ≫ k = (C.geometricSpecialKernel R L q A ρ J.val true).inclusion :=
    C.geometricMixedLine_inclusion R L q A ρ J
  exact (Category.assoc u v h).trans ((congrArg (fun f => u ≫ f) hv).trans
    ((Category.assoc u k a.hom.hom.hom).symm.trans (congrArg (fun f => f ≫ a.hom.hom.hom) hu)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
