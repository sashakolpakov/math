import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedActive
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.XZFactors
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

/-! # Reduced XZ Point -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXZPoint

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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCoordinates.X OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.XZFactors OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrescribedCompositePointIsogeny
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

include hC0 QX hFrob in
theorem originalReducedPoint_eq_XZ
    (p : ULift (Fin (a.evaluation.count (some 2))))
    (hV : CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 2 p = ⊤)
    (hflag : CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 2 p = true)
    (QZ : D.PrescribedOrdinaryQuotient y (q ^ 2)
      (D.prescribedFullZKernel j iota hsplit labels O C0 y) z) :
    ReducedPoint.originalReducedPoint j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood hbase = z.val := by
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let f := ReducedPoint.originalReducedPointIsogeny j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood hbase
  let g := PrescribedCompositePointIsogeny.prescribedCompositePointIsogeny QX QZ
  apply PointIsogenyComparison.point_eq_of_isogeny_chosen hgood j hsplit labels hlabels 3 f g
    (SpecialPointBound.originalSpecialPoint_kernel_bound j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood hbase)
    (PrescribedCompositePointIsogeny.prescribedCompositePointIsogeny_kernel_bound j hsplit labels
      (D.prescribedXChosen j iota hsplit labels O C0 x)
      (D.prescribedZChosen j iota hsplit labels O C0 y) QX QZ) ?_
  intro v T b hb
  cases v using Fin.cases with
  | zero =>
    have h := ReducedActive.originalReducedPoint_full_active
      j hsplit labels O l hTorsionQuotient a hlabels hgood hbase p hV hflag T b.val hb
    exact h.trans
      (Canonical.XZFactors.canonicalXZ_active_factor j hsplit labels O C0 QX hFrob QZ T b.val b.property hb).symm
  | succ w =>
    have h := SpecialPointCompact.originalSpecialPoint_compact_iff j hsplit labels O l hTorsionQuotient a hlabels
      2 p hgood hbase w T b.val hb
    have hc := PrescribedCompositeCompact.prescribedComposite_compact_kernel j hsplit labels O C0 QX hFrob hC0
      (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveZChosenSubgroup j iota hsplit (D.pointDatum y.val).data.polarized
        (D.pointDatum y.val).data.action (labels (0, false)) (O.splitting y 1 0)) QZ w T b.val hb
    exact h.trans hc.symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXZPoint
