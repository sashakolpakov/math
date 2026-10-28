import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.EtaleLineInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PulledOrdinaryFactorInclusion

/-! # Graph Line Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.GraphLineKernel.Lifts

noncomputable section

/-! A specialized original graph line is the chosen native etale line
in the constructed geometric ordinary chart, including its inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.EtaleLineInclusion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PulledOrdinaryFactorInclusion.Ordinary
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

private theorem graph_zero_eq_splitSecond {S : Scheme} {M E A H : Grp (Over S)}
    (s : M ⊗ E ≅ A) (i : H ⟶ E) :
    QuotientGraphs.graphKernel s.hom.hom.hom i.hom.hom 1 = (i ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion M E ≫ s.hom).hom.hom := by
  change lift (1 : H.X ⟶ M.X) i.hom.hom ≫ s.hom.hom.hom =
    i.hom.hom ≫ lift (1 : E.X ⟶ M.X) (𝟙 E.X) ≫ s.hom.hom.hom
  rw [← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id]

variable (R L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] (q : ℕ) [Fact q.Prime]
  (A : Grp (Over (Spec (.of R)))) (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q A)
  (ρ : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R)

theorem _root_.OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricEtalePlane_inclusion :
    (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricEtaleIso R q ρ).hom ≫
      AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) =
      (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ))).mapGrp.map
        (AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion C.identity
          (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))) ≫ C.split.hom) :=
  PulledOrdinaryFactorInclusion.Ordinary.pulledSplitSecond_inclusion (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) C.split
    (C.geometricIdentityIso R L q A ρ) (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricEtaleIso R q ρ)

theorem _root_.OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricGraphLine_inclusion (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (EtaleLineInclusion.geometricEtaleLineIso (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)) q J).hom.hom.hom ≫
      (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) J).hom.hom =
      (C.geometricSpecialKernel R L q A ρ J.val false).inclusion := by
  let f := Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := ρ)
  let F := (Over.pullback f).mapGrp
  let k := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupMap (Spec (.of R)) J.val.subtype.toAddMonoidHom.toMultiplicative
  let p := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ)
  have hi := EtaleLineInclusion.geometricEtaleLineIso_inclusion f q J
  have hp := C.geometricEtalePlane_inclusion R L q A ρ
  have h : (EtaleLineInclusion.geometricEtaleLineIso f q J).hom ≫
      AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (C.geometricSplitting R L q A ρ) J =
      F.map (k ≫ AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion C.identity
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative (Fin 2 → ZMod q))) ≫ C.split.hom) := by
    change (EtaleLineInclusion.geometricEtaleLineIso f q J).hom ≫ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding _ q J ≫ p = _
    rw [← Category.assoc, hi, Category.assoc]
    change F.map k ≫ (OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricEtaleIso R q ρ).hom ≫ p = _
    rw [hp, ← F.map_comp]
  have hz := graph_zero_eq_splitSecond C.split k
  exact (congrArg (fun u => u.hom.hom) h).trans
    (congrArg (fun u => (Over.pullback f).map u) hz.symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.GraphLineKernel.Lifts
