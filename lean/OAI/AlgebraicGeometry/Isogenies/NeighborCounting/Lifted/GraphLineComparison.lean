import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.GraphIndependentLine
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockInclusions
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting

/-! # Graph Line Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GraphLineComparison

noncomputable section

/-! The original integral graph-line inclusion is identified inside the
actual source PEL point, using the independently prescribed ordinary chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockInclusions

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)

variable {L : Type} [Field L] [Algebra R L]
  (C : OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel R L q (OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels l))

local notation "A" => OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels l
local notation "e" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0)
local notation "a" => OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockInclusions.liftedGeometricOriginalBlockIso j hsplit labels l 1 0

def liftedCoordinateLineEquiv : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q ≃ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q :=
  C.geometricLineEquiv R L q A residueIso e a

def liftedGraphIndependentLineIso (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).mapGrp.obj
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative J.val)) ≅
      AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q
        (liftedCoordinateLineEquiv j hsplit labels O l C J) :=
  C.geometricGraphIndependentLineIso R L q A residueIso e a J

theorem liftedGraphLine_ambient_inclusion (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (liftedGraphIndependentLineIso j hsplit labels O l C J).hom.hom.hom ≫
      (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e
        (liftedCoordinateLineEquiv j hsplit labels O l C J)).hom.hom ≫
          AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
            (D.pointDatum x.val).data.action 1 (labels (0, false)) =
    (C.geometricSpecialKernel R L q A residueIso J.val false).inclusion ≫
      (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1)
          (l.action.map (j.projector iota hsplit 1 (labels (0, false))))) ≫
            l.geometricFamilyIso.abelian.hom := by
  let u := (liftedGraphIndependentLineIso j hsplit labels O l C J).hom.hom.hom
  let k := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q e
    (liftedCoordinateLineEquiv j hsplit labels O l C J)).hom.hom
  let g := (C.geometricSpecialKernel R L q A residueIso J.val false).inclusion
  let b0 := AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action 1 (labels (0, false))
  let t := (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false)))))
  have hi : u ≫ k = g ≫ (a).hom.hom.hom :=
    C.geometricGraphIndependentLine_inclusion R L q A residueIso e a J
  have ha : (a).hom.hom.hom ≫ b0 = t ≫ l.geometricFamilyIso.abelian.hom :=
    Geometric.BlockInclusions.liftedGeometricOriginalBlockIso_inclusion j hsplit labels l 1 0
  exact (Category.assoc u k b0).symm.trans
    ((congrArg (fun f => f ≫ b0) hi).trans
      ((Category.assoc g (a).hom.hom.hom b0).trans (congrArg (fun f => g ≫ f) ha)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GraphLineComparison
