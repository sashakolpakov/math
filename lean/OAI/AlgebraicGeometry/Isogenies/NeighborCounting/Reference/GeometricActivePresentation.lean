import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.LiteralCoordinatePointPresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.ActivePointPresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveSpecialKernels

/-! # Geometric Active Presentation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GeometricActivePresentation

noncomputable section

/-! The actual original active point presentation specializes to the
constructed graph or mixed subgroup, with the full ambient inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotients OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier.ReferencePresentation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveSpecialKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
attribute [local instance] Classical.propDecidable

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

variable (a : ConstructedActiveEvaluation.LiftedActiveEvaluation (L := L) j hsplit labels O l hTorsionQuotient)

variable (i : Fin 3) (p : ULift (Fin (a.evaluation.count (some i))))

attribute [local irreducible] OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel
  OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricSpecialKernel EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel
  CoordinateSubspaces.originalCoordinateKernelParameters

def originalGeometricActivePresentation :
    Intrinsic.Neighbors.KernelPresentation (Intrinsic.QuotientTargets.geometricFamily (D.pointDatum x.val)).abelian.scheme :=
    letI := a.evaluation.scalarAlgebra R
    letI := a.evaluation.scalarTower R
    let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
    let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
    let J := (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val
    (C.geometricSpecialKernel v.carrier a.evaluation.carrier q _ (residueIso.trans v.residueIso)
      (J.map (LinearMap.fst (ZMod q) (Fin 2 → ZMod q) (ZMod q)))
      (decide (SubspaceCounts.Construction.identityLine ≤ J))).postcomp
        ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))).map
          (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) ((l.overEvaluationDVR v).action.map
            (j.projector iota hsplit 1 (labels (0, false))))) ≫
              (l.overEvaluationDVR v).geometricFamilyIso.abelian.hom)

theorem originalActivePointPresentation_geometric :
    type_of% (
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  let J := (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val
  C.finiteFlatKernel_literal_geometricPointPresentation v.carrier a.evaluation.carrier q _
    (residueIso.trans v.residueIso)
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) ((l.overEvaluationDVR v).action.map
      (j.projector iota hsplit 1 (labels (0, false)))))
    (l.overEvaluationDVR v).geometricFamilyIso.abelian.hom J) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l v a.blockIso
  let J := (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val
  exact C.finiteFlatKernel_literal_geometricPointPresentation v.carrier a.evaluation.carrier q _
    (residueIso.trans v.residueIso)
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) ((l.overEvaluationDVR v).action.map
      (j.projector iota hsplit 1 (labels (0, false)))))
    (l.overEvaluationDVR v).geometricFamilyIso.abelian.hom J

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GeometricActivePresentation
