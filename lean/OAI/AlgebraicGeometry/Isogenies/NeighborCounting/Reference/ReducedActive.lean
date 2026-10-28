import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.Criterion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FixedKernelCriterion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeNormalization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedCoordinateKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinatePointFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.SpecialPointBound
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.SpecialPointCompact
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCompactPoint
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralKernelPresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.SpecialPointIsogeny

/-! # Reduced Active -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedActive

noncomputable section

/-! The original multiplicative line specialization has the independent
canonical X quotient point, with its full positive PEL kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotients OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotientKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicNeighbors.ReferenceIntrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericSameKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralKernelPresentation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.QuotientTargets
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny.KernelBound

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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedPoint OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedCoordinateKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinatePointFactors.ReferencePresentation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinatePointFactors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.SpecialPointBound OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.SpecialPointCompact
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCompactPoint

variable (hlabels : ∀ v : Fin (s + 1),
  labels (v, true) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, false))
  (C0 : D.CompactKernelPrescription j iota hsplit labels)
  (hC0 : D.CompactKernelCondition j iota hsplit labels O C0)
  (hgood : D.IsGoodCompletelySplitReduction)
  (hbase : Lifts.ResidueCompatible D R b residueIso)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeNormalization

attribute [local irreducible] OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel
  OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricSpecialKernel
  OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricLineEquiv
  EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel
  ConstructedActiveEvaluation.activeEvaluationDVR Lifts.IntegralLift.overEvaluationDVR IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor CoordinateSubspaces.originalCoordinateKernelParameters

attribute [local irreducible] Intrinsic.Neighbors.KernelPresentation.KernelOnFixed
  Evaluated.PointIsogeny.Lifts.evaluatedPointIsogeny

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralSpecialActiveCriteria

theorem originalReducedPoint_full_active
    (p : ULift (Fin (a.evaluation.count (some 2))))
    (hV : CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 2 p = ⊤)
    (hflag : CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 2 p = true) :
    type_of% (show _ from by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let Q := IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L)
    j hsplit labels O l v a.blockIso
  let W := (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 2 p).val
  exact Evaluated.Criterion.evaluatedPointIsogeny_full_criterion
    j hsplit labels (l.overEvaluationDVR v) Q.target (ConstructedEvaluation.Lifts.evaluation_residueCompatible v hbase)
    (IntegralQuotientKernel.originalIntegralModelIsogeny j hsplit labels O l hTorsionQuotient a hlabels 2 p)
    (GenericSameKernel.originalGenericPELBetweenModels j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood)
    (GenericSameKernel.originalGenericSameKernel j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood)
    (D.levelPrimeToQ.pow_left (HeckeExponents.neighborLevel 2))
    (IntegralKernelPresentation.originalIntegralKernelBound j hsplit labels O l hTorsionQuotient a hlabels 2 p)
    (j.projector iota hsplit (HeckeExponents.neighborLevel 2) (labels (0, false)))
    (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a 2 p)
    (IntegralSpecialActiveCriteria.originalIntegralSpecial_active_factor j hsplit labels O l hTorsionQuotient a hlabels 2 p)
    C W hV hflag
    (SpecialPresentationEquality.originalSpecialPresentation_eq_coordinate_source
      j hsplit labels O l hTorsionQuotient a 2 p)) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let Q := IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L)
    j hsplit labels O l v a.blockIso
  let W := (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 2 p).val
  exact Evaluated.Criterion.evaluatedPointIsogeny_full_criterion
    j hsplit labels (l.overEvaluationDVR v) Q.target (ConstructedEvaluation.Lifts.evaluation_residueCompatible v hbase)
    (IntegralQuotientKernel.originalIntegralModelIsogeny j hsplit labels O l hTorsionQuotient a hlabels 2 p)
    (GenericSameKernel.originalGenericPELBetweenModels j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood)
    (GenericSameKernel.originalGenericSameKernel j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood)
    (D.levelPrimeToQ.pow_left (HeckeExponents.neighborLevel 2))
    (IntegralKernelPresentation.originalIntegralKernelBound j hsplit labels O l hTorsionQuotient a hlabels 2 p)
    (j.projector iota hsplit (HeckeExponents.neighborLevel 2) (labels (0, false)))
    (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a 2 p)
    (IntegralSpecialActiveCriteria.originalIntegralSpecial_active_factor j hsplit labels O l hTorsionQuotient a hlabels 2 p)
    C W hV hflag
    (SpecialPresentationEquality.originalSpecialPresentation_eq_coordinate_source
      j hsplit labels O l hTorsionQuotient a 2 p)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedActive
