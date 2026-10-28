import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.MultiplicativeCriterion
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

/-! # Reference Reduced Active -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedActive.ReferenceX

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

theorem originalReducedPoint_X_active
    (p : ULift (Fin (a.evaluation.count (some 0))))
    (hV : CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 0 p = ⊥)
    (hflag : CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 0 p = true) :
    type_of% (show _ from by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let Q := IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L)
    j hsplit labels O l v a.blockIso
  let J := (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 0 p).val
  exact Evaluated.MultiplicativeCriterion.evaluatedPointIsogeny_multiplicative_criterion
    j hsplit labels O (l.overEvaluationDVR v) Q.target (ConstructedEvaluation.Lifts.evaluation_residueCompatible v hbase)
    (IntegralQuotientKernel.originalIntegralModelIsogeny j hsplit labels O l hTorsionQuotient a hlabels 0 p)
    (GenericSameKernel.originalGenericPELBetweenModels j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood)
    (GenericSameKernel.originalGenericSameKernel j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood)
    (D.levelPrimeToQ.pow_left (HeckeExponents.neighborLevel 0))
    (IntegralKernelPresentation.originalIntegralKernelBound j hsplit labels O l hTorsionQuotient a hlabels 0 p)
    (j.projector iota hsplit (HeckeExponents.neighborLevel 0) (labels (0, false)))
    (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a 0 p)
    (IntegralSpecialActiveCriteria.originalIntegralSpecial_active_factor j hsplit labels O l hTorsionQuotient a hlabels 0 p)
    C J hV hflag
    (SpecialPresentationEquality.originalSpecialPresentation_eq_coordinate_source
      j hsplit labels O l hTorsionQuotient a 0 p)) := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let Q := IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L)
    j hsplit labels O l v a.blockIso
  let J := (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 0 p).val
  exact Evaluated.MultiplicativeCriterion.evaluatedPointIsogeny_multiplicative_criterion
    j hsplit labels O (l.overEvaluationDVR v) Q.target (ConstructedEvaluation.Lifts.evaluation_residueCompatible v hbase)
    (IntegralQuotientKernel.originalIntegralModelIsogeny j hsplit labels O l hTorsionQuotient a hlabels 0 p)
    (GenericSameKernel.originalGenericPELBetweenModels j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood)
    (GenericSameKernel.originalGenericSameKernel j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood)
    (D.levelPrimeToQ.pow_left (HeckeExponents.neighborLevel 0))
    (IntegralKernelPresentation.originalIntegralKernelBound j hsplit labels O l hTorsionQuotient a hlabels 0 p)
    (j.projector iota hsplit (HeckeExponents.neighborLevel 0) (labels (0, false)))
    (IntegralSpecialActiveCriteria.originalActiveSpecialPresentation j hsplit labels O l hTorsionQuotient a 0 p)
    (IntegralSpecialActiveCriteria.originalIntegralSpecial_active_factor j hsplit labels O l hTorsionQuotient a hlabels 0 p)
    C J hV hflag
    (SpecialPresentationEquality.originalSpecialPresentation_eq_coordinate_source
      j hsplit labels O l hTorsionQuotient a 0 p)

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedActive.ReferenceX

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedActive.ReferenceXPoint

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

include hC0 in
theorem originalReducedPoint_eq_X
    (p : ULift (Fin (a.evaluation.count (some 0))))
    (hV : CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 0 p = ⊥)
    (hflag : CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 0 p = true)
    {y : D.OrdinaryPoint}
    (QX : D.PrescribedOrdinaryQuotient x q
      (D.prescribedFullXKernel j iota hsplit labels O C0 x) y) :
    ReducedPoint.originalReducedPoint j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood hbase = y.val := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let H0 := AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup (O.splitting x 1 0)
  have Qn : D.PrescribedOrdinaryQuotient x (q ^ 1)
      (AbelianScheme.FrobeniusKernel.Prescription.Construction.prescribedFullKernel j iota hsplit (D.pointDatum x.val).data.polarized
        (D.pointDatum x.val).data.action 1 (s + 1) labels (Fin.cases H0 (C0 x 1))) y := by
    change D.PrescribedOrdinaryQuotient x (q ^ 1)
      (D.prescribedFullXKernel j iota hsplit labels O C0 x) y
    exact (congrArg (fun m => D.PrescribedOrdinaryQuotient x m
      (D.prescribedFullXKernel j iota hsplit labels O C0 x) y) (pow_one q)).mpr QX
  let f := ReducedPoint.originalReducedPointIsogeny j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood hbase
  apply Canonical.ActiveCompactPoint.point_eq_of_active_and_compact j hsplit labels hlabels O C0 hC0 1 H0 Qn f
    (SpecialPointBound.originalSpecialPoint_kernel_bound j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood hbase)
    ?_ ?_ hgood
  · exact ReferenceX.originalReducedPoint_X_active
      j hsplit labels O l hTorsionQuotient a hlabels hgood hbase p hV hflag
  · intro w
    exact SpecialPointCompact.originalSpecialPoint_compact_iff j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood hbase w

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedActive.ReferenceXPoint

end

end OAI
