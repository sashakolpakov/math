import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointCoordinateCriteria
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointNamedActiveCriteria
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.SpecialPointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier

/-! # Point Coordinate Criterion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.PointCoordinateCriterion

noncomputable section

/-! Every original special PEL neighbor has the actual specialized
active carrier. Its criterion is discharged by the constructed original
integral quotient on the geometric special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotients OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotientKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicNeighbors.ReferenceIntrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericSameKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralKernelPresentation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointNamedActiveCriteria OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier.ReferencePresentation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActivePointCarrier

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

variable (hgood : D.IsGoodCompletelySplitReduction)

variable (hbase : Lifts.ResidueCompatible D R b residueIso)

attribute [local irreducible] IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor
  Kernel.Base.fullKernel AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
  IntegralCanonicalNeighbors.integralCanonicalQuotient
  Lifts.IntegralLift.canonicalIntegralQuotient IntegralActiveKernels.originalIntegralActiveKernel
  IntegralSpecialActiveCriteria.originalActiveSpecialPresentation ConstructedActiveEvaluation.activeEvaluationDVR Lifts.IntegralLift.overEvaluationDVR

theorem originalPoint_coordinate_criterion :
    type_of% (show _ from by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let Q := IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels i p hgood
  exact Evaluated.PointCoordinateCriteria.evaluatedPointIsogeny_coordinate_criterion
    (l.overEvaluationDVR v) Q.target (ConstructedEvaluation.Lifts.evaluation_residueCompatible v hbase)
    (IntegralQuotientKernel.originalIntegralModelIsogeny j hsplit labels O l hTorsionQuotient a hlabels i p)
    (GenericSameKernel.originalGenericPELBetweenModels j hsplit labels O l hTorsionQuotient a hlabels i p hgood)
    (GenericSameKernel.originalGenericSameKernel j hsplit labels O l hTorsionQuotient a hlabels i p hgood)
    (D.levelPrimeToQ.pow_left (HeckeExponents.neighborLevel i))
    (IntegralKernelPresentation.originalIntegralKernelBound j hsplit labels O l hTorsionQuotient a hlabels i p)
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (0, false)))
    (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a i p)
    (IntegralSpecialActiveCriteria.originalIntegralSpecial_active_factor j hsplit labels O l hTorsionQuotient a hlabels i p)
    (G := Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels (l.overEvaluationDVR v))) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let Q := IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels i p hgood
  exact Evaluated.PointCoordinateCriteria.evaluatedPointIsogeny_coordinate_criterion
    (l.overEvaluationDVR v) Q.target (ConstructedEvaluation.Lifts.evaluation_residueCompatible v hbase)
    (IntegralQuotientKernel.originalIntegralModelIsogeny j hsplit labels O l hTorsionQuotient a hlabels i p)
    (GenericSameKernel.originalGenericPELBetweenModels j hsplit labels O l hTorsionQuotient a hlabels i p hgood)
    (GenericSameKernel.originalGenericSameKernel j hsplit labels O l hTorsionQuotient a hlabels i p hgood)
    (D.levelPrimeToQ.pow_left (HeckeExponents.neighborLevel i))
    (IntegralKernelPresentation.originalIntegralKernelBound j hsplit labels O l hTorsionQuotient a hlabels i p)
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (0, false)))
    (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a i p)
    (IntegralSpecialActiveCriteria.originalIntegralSpecial_active_factor j hsplit labels O l hTorsionQuotient a hlabels i p)
    (G := Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels (l.overEvaluationDVR v))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.PointCoordinateCriterion
