import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedMixedActive
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupTensorFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.XYFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositeCompact
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointIsogenyComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedCoordinateKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinatePointFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.SpecialPointBound
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.SpecialPointCompact
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCompactPoint
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralKernelPresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.SpecialPointIsogeny

/-! # Reduced XY Point -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXYPoint

noncomputable section

/-! Every original disjoint active line specializes to the independent
canonical Y quotient at its constructed geometric line label. -/

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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCoordinates.X OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.XYFactors OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositePointIsogeny
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositeCompact OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointIsogenyComparison

variable {y z : D.OrdinaryPoint}
  (QX : D.PrescribedOrdinaryQuotient x q (D.prescribedFullXKernel j iota hsplit labels O C0 x) y)
  (hFrob : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    D.prescribedFullXKernel j iota hsplit labels O C0 x T a ↔ D.relativeFrobeniusKernelCondition x T a)

attribute [local irreducible] OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel
  OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricSpecialKernel
  OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.geometricLineEquiv
  EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel
  ConstructedActiveEvaluation.activeEvaluationDVR Lifts.IntegralLift.overEvaluationDVR IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor CoordinateSubspaces.originalCoordinateKernelParameters

include hC0 in
theorem originalReducedPoint_eq_XY
    (p : ULift (Fin (a.evaluation.count (some 1)))) (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (hJ : CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 1 p = J.val)
    (hflag : CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 1 p = true)
    (QY : D.PrescribedOrdinaryQuotient y q
      (D.prescribedFullYKernel j iota hsplit labels O C0 y
        (Canonical.ActiveCoordinates.X.canonicalXLineEquiv j hsplit labels O C0 QX hFrob
          (CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv j hsplit labels O l hTorsionQuotient a J))) z) :
    ReducedPoint.originalReducedPoint j hsplit labels O l hTorsionQuotient a hlabels 1 p hgood hbase = z.val := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let J0 := CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv j hsplit labels O l hTorsionQuotient a J
  let J1 := Canonical.ActiveCoordinates.X.canonicalXLineEquiv j hsplit labels O C0 QX hFrob J0
  have Q1 : D.PrescribedOrdinaryQuotient y (q ^ 1)
      (D.prescribedFullYKernel j iota hsplit labels O C0 y J1) z := by
    exact (congrArg (fun m => D.PrescribedOrdinaryQuotient y m
      (D.prescribedFullYKernel j iota hsplit labels O C0 y J1) z) (pow_one q)).mpr QY
  let f := ReducedPoint.originalReducedPointIsogeny j hsplit labels O l hTorsionQuotient a hlabels 1 p hgood hbase
  let g := PrescribedCompositePointIsogeny.prescribedCompositePointIsogeny QX Q1
  apply PointIsogenyComparison.point_eq_of_isogeny_chosen hgood j hsplit labels hlabels 2 f g
    (SpecialPointBound.originalSpecialPoint_kernel_bound j hsplit labels O l hTorsionQuotient a hlabels 1 p hgood hbase)
    (PrescribedCompositePointIsogeny.prescribedCompositePointIsogeny_kernel_bound j hsplit labels
      (D.prescribedXChosen j iota hsplit labels O C0 x)
      (D.prescribedYChosen j iota hsplit labels O C0 y J1) QX Q1) ?_
  intro v T b hb
  cases v using Fin.cases with
  | zero =>
    have h := ReducedMixedActive.originalReducedPoint_mixed_active
      j hsplit labels O l hTorsionQuotient a hlabels hgood hbase p J hJ hflag T b.val hb
    have hc := Canonical.XYFactors.canonicalXY_active_factor j hsplit labels O C0 QX hFrob J0 Q1 T b.val b.property hb
    have ht := GroupTensorFactors.tensor_carrier_factor_iff
      (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q 1 1)
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) q J0)
      ((ActiveMixedLineTransport.chosenActiveMixedLine (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q
        (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q (O.splitting x 1 0)) J0).hom.hom ≫
        AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
          (D.pointDatum x.val).data.action 1 (labels (0, false))) T b.val
    exact h.trans (hc.trans ht).symm
  | succ w =>
    have h := SpecialPointCompact.originalSpecialPoint_compact_iff j hsplit labels O l hTorsionQuotient a hlabels
      1 p hgood hbase w T b.val hb
    have hc := PrescribedCompositeCompact.prescribedComposite_compact_kernel j hsplit labels O C0 QX hFrob hC0
      (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveYChosenSubgroup j iota hsplit (D.pointDatum y.val).data.polarized
        (D.pointDatum y.val).data.action (labels (0, false)) (O.splitting y 1 0) J1) Q1 w T b.val hb
    exact h.trans hc.symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXYPoint
