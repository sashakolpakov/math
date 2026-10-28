import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.PresentationComposition
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.SpecialActiveKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralKernelPresentation

/-! # Integral Special Active Criteria -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria

noncomputable section

/-! The literal original integral neighbor has the actual specialized
active carrier and inclusion on its geometric special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotients OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralSpecialChosenKernel

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

variable (hlabels : ∀ v : Fin (s + 1),
  labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (i : Fin 3) (p : ULift (Fin (a.evaluation.count (some i))))

attribute [local irreducible] Kernel.Base.fullKernel AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
  AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion
  IntegralCanonicalNeighbors.integralCanonicalQuotient CoordinateSubspaces.originalCoordinateKernelParameters
  Joint.KernelParameters.jointKernelParameters
  Evaluated.ActiveParameterFamily.SourceFamilies.evaluatedIntegralActiveSourceFamily
  Lifts.IntegralLift.canonicalIntegralQuotient IntegralActiveKernels.originalIntegralActiveKernel

def originalActiveSpecialCarrier : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))).obj
    (IntegralActiveKernels.originalIntegralActiveKernel j hsplit labels O l hTorsionQuotient a i p).carrier

def originalActiveSpecialInclusion :
    letI := a.evaluation.scalarAlgebra R
    letI := a.evaluation.scalarTower R
    let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
    originalActiveSpecialCarrier j hsplit labels O l hTorsionQuotient a i p ⟶
      ((ActionFamilyComparison.Family.actionFamily (l.overEvaluationDVR v).actionData).pullback
        (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))).abelian.scheme :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))).map
    ((IntegralActiveKernels.originalIntegralActiveKernel j hsplit labels O l hTorsionQuotient a i p).inclusion ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) ((l.overEvaluationDVR v).action.map
        (j.projector iota hsplit 1 (labels (0, false)))))

def originalActiveSpecialPresentation :
    letI := a.evaluation.scalarAlgebra R
    letI := a.evaluation.scalarTower R
    let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
    Intrinsic.Neighbors.KernelPresentation ((ActionFamilyComparison.Family.actionFamily (l.overEvaluationDVR v).actionData).pullback
      (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))).abelian.scheme :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let P : Intrinsic.Neighbors.KernelPresentation
      (ActionFamilyComparison.Family.actionFamily (l.overEvaluationDVR v).actionData).abelian.scheme :=
    (IntegralActiveKernels.originalIntegralActiveKernel j hsplit labels O l hTorsionQuotient a i p).toKernelPresentation.postcomp
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) ((l.overEvaluationDVR v).action.map
        (j.projector iota hsplit 1 (labels (0, false)))))
  P.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))

theorem originalIntegralSpecial_active_factor :
    letI := a.evaluation.scalarAlgebra R
    letI := a.evaluation.scalarTower R
    let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
    ∀ (T : Over (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))))
      (z : T ⟶ ((ActionFamilyComparison.Family.actionFamily (l.overEvaluationDVR v).actionData).pullback
        (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))).abelian.scheme),
      z ≫ (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))).map
        ((l.overEvaluationDVR v).action.map
          (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (0, false)))) = z →
      (z ≫ ((IntegralQuotientKernel.originalIntegralModelIsogeny
        j hsplit labels O l hTorsionQuotient a hlabels i p).pullback
          (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso.trans v.residueIso))).hom = 1 ↔
        ∃ h : T ⟶ (originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a i p).carrier,
          h ≫ (originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a i p).inclusion = z) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  delta IntegralQuotientKernel.originalIntegralModelIsogeny IntegralQuotients.originalIntegralQuotient
    originalActiveSpecialPresentation
  have h := (l.overEvaluationDVR v).canonicalSpecial_active_factor j hsplit labels hlabels
    (HeckeExponents.neighborLevel i) (Nat.succ_le_succ (Nat.zero_le i.val)) 0 (Fin.cases false (O.compact x))
    (IntegralActiveKernels.originalIntegralActiveKernel j hsplit labels O l hTorsionQuotient a i p)
  exact h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria
