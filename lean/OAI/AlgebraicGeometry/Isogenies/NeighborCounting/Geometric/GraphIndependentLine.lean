import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.GraphLineKernel

/-! # Graph Independent Line -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The specialized original graph line is identified with the line in
an independent ordinary chart by the constructed permutation of lines. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.EtaleLineInclusion

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)
  {B : Grp (Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))}
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q B)
  (a : (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj A ≅ B)

def OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricGraphIndependentLineIso (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.obj
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative J.val)) ≅
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q
        (C.geometricLineEquiv R L q A ρ e a J) :=
  Geometric.EtaleLineInclusion.geometricEtaleLineIso (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) q J ≪≫
    C.geometricLineIso R L q A ρ e a J

theorem OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricGraphIndependentLine_inclusion (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (C.geometricGraphIndependentLineIso R L q A ρ e a J).hom.hom.hom ≫
      (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e (C.geometricLineEquiv R L q A ρ e a J)).hom.hom =
      (C.geometricSpecialKernel R L q A ρ J.val false).inclusion ≫ a.hom.hom.hom := by
  let u := (Geometric.EtaleLineInclusion.geometricEtaleLineIso (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) q J).hom.hom.hom
  let v := (C.geometricLineIso R L q A ρ e a J).hom.hom.hom
  let k := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q
    (C.geometricSplitting R L q A ρ) J).hom.hom
  let h := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e
    (C.geometricLineEquiv R L q A ρ e a J)).hom.hom
  have hv : v ≫ h = k ≫ a.hom.hom.hom :=
    congrArg (fun f => f.hom.hom) (C.geometricLineIso_inclusion R L q A ρ e a J)
  have hu : u ≫ k = (C.geometricSpecialKernel R L q A ρ J.val false).inclusion :=
    C.geometricGraphLine_inclusion R L q A ρ J
  exact (Category.assoc u v h).trans ((congrArg (fun f => u ≫ f) hv).trans
    ((Category.assoc u k a.hom.hom.hom).symm.trans
      (congrArg (fun f => f ≫ a.hom.hom.hom) hu)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
