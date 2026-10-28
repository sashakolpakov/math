import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedActive
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedPoint
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedZ
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXYPoint
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXZPoint
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues
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
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport

/-! # Parameter Eq -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterEq.ReferencePoints

/-! Every original disjoint active line specializes to the independent
canonical Y quotient at its constructed geometric line label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCoordinates.X OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues.CoordinateCases
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedActive.ReferenceXPoint OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedPoint.ReferenceY OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedZ.ReferencePoint
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXYPoint OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXZPoint

variable (X0 : D.OrdinaryPoint → D.OrdinaryPoint)
  (Yquotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
  (Z0 : D.OrdinaryPoint → D.OrdinaryPoint)
  (QX : D.PrescribedOrdinaryQuotient x q (D.prescribedFullXKernel j iota hsplit labels O C0 x) (X0 x))
  (hY : ∀ y J, D.CanonicalOrdinaryQuotient y q
    (D.prescribedFullYKernel j iota hsplit labels O C0 y J) (Yquotient y J))
  (hZ : ∀ y, D.CanonicalOrdinaryQuotient y (q ^ 2)
    (D.prescribedFullZKernel j iota hsplit labels O C0 y) (Z0 y))
  (hFrob : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    D.prescribedFullXKernel j iota hsplit labels O C0 x T a ↔ D.relativeFrobeniusKernelCondition x T a)

def originalCanonicalParameterValue :=
  Parameter.CanonicalValues.canonicalParameterValue (X0 x).val (Z0 x).val (Z0 (X0 x)).val
    (fun J => (Yquotient x J).val) (fun J => (Yquotient (X0 x) J).val)
    (CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv j hsplit labels O l hTorsionQuotient a)
    ((CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv j hsplit labels O l hTorsionQuotient a).trans
      (Canonical.ActiveCoordinates.X.canonicalXLineEquiv j hsplit labels O C0 QX hFrob))

attribute [local irreducible] ReducedPoint.originalReducedPoint CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv
  IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor CoordinateSubspaces.originalCoordinateKernelParameters
  Canonical.ActiveCoordinates.X.canonicalXLineEquiv

include hY hC0 in
theorem originalReducedPoint_parameter_value_zero
    (p : ULift (Fin (a.evaluation.count (some 0)))) :
    ReducedPoint.originalReducedPoint j hsplit labels O l hTorsionQuotient a hlabels 0 p hgood hbase =
      originalCanonicalParameterValue j hsplit labels O l hTorsionQuotient a C0 X0 Yquotient Z0 QX hFrob 0
        (CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 0 p)
        (CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 0 p) := by
  classical
  unfold originalCanonicalParameterValue
  rcases Parameter.CanonicalValues.CoordinateCases.line_projection_cases
      (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 0 p).val
      (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 0 p).property with
      ⟨hp, hf⟩ | ⟨J, hp, hf⟩
  · change CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 0 p = ⊥ at hp
    change CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 0 p = true at hf
    have h := ReferenceReducedActive.ReferenceXPoint.originalReducedPoint_eq_X j hsplit labels O l hTorsionQuotient a hlabels C0 hC0 hgood hbase p hp hf QX
    simpa only [Parameter.CanonicalValues.canonicalParameterValue_zero, hf, ↓reduceIte] using h
  · change CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 0 p = J.val at hp
    change CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 0 p = false at hf
    have h := ReferenceReducedPoint.ReferenceY.originalReducedPoint_eq_Y j hsplit labels O l hTorsionQuotient a hlabels C0 hC0 hgood hbase p J hp hf
      (Classical.choice (hY x (CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv j hsplit labels O l hTorsionQuotient a J)).1)
    simpa only [Parameter.CanonicalValues.canonicalParameterValue_zero, hp, hf, Bool.false_eq_true, ↓reduceIte,
      Parameter.CanonicalValues.lineParameterValue_line] using h

include hY hZ hC0 in
theorem originalReducedPoint_parameter_value_one
    (p : ULift (Fin (a.evaluation.count (some 1)))) :
    ReducedPoint.originalReducedPoint j hsplit labels O l hTorsionQuotient a hlabels 1 p hgood hbase =
      originalCanonicalParameterValue j hsplit labels O l hTorsionQuotient a C0 X0 Yquotient Z0 QX hFrob 1
        (CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 1 p)
        (CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 1 p) := by
  classical
  unfold originalCanonicalParameterValue
  rcases Parameter.CanonicalValues.CoordinateCases.plane_projection_cases
      (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 1 p).val
      (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 1 p).property with
      ⟨J, hp, hf⟩ | ⟨hp, hf⟩
  · change CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 1 p = J.val at hp
    change CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 1 p = true at hf
    have h := ReducedXYPoint.originalReducedPoint_eq_XY j hsplit labels O l hTorsionQuotient a hlabels C0 hC0 hgood hbase
      QX hFrob p J hp hf
      (Classical.choice (hY (X0 x) (Canonical.ActiveCoordinates.X.canonicalXLineEquiv j hsplit labels O C0 QX hFrob
        (CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv j hsplit labels O l hTorsionQuotient a J))).1)
    simpa only [Parameter.CanonicalValues.canonicalParameterValue_one, hp, hf, ↓reduceIte,
      Parameter.CanonicalValues.lineParameterValue_line, Equiv.trans_apply] using h
  · change CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 1 p = ⊤ at hp
    change CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 1 p = false at hf
    have h := ReducedZ.ReferencePoint.originalReducedPoint_eq_Z j hsplit labels O l hTorsionQuotient a hlabels C0 hC0 hgood hbase
      p hp hf (Classical.choice (hZ x).1)
    simpa only [Parameter.CanonicalValues.canonicalParameterValue_one, hf, Bool.false_eq_true, ↓reduceIte] using h

include hZ hC0 in
theorem originalReducedPoint_parameter_value_two
    (p : ULift (Fin (a.evaluation.count (some 2)))) :
    ReducedPoint.originalReducedPoint j hsplit labels O l hTorsionQuotient a hlabels 2 p hgood hbase =
      originalCanonicalParameterValue j hsplit labels O l hTorsionQuotient a C0 X0 Yquotient Z0 QX hFrob 2
        (CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 2 p)
        (CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 2 p) := by
  classical
  unfold originalCanonicalParameterValue
  obtain ⟨hp, hf⟩ := Parameter.CanonicalValues.CoordinateCases.full_projection_case
    (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 2 p).val
    (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a 2 p).property
  change CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a 2 p = ⊤ at hp
  change CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a 2 p = true at hf
  exact ReducedXZPoint.originalReducedPoint_eq_XZ j hsplit labels O l hTorsionQuotient a hlabels C0 hC0 hgood hbase
    QX hFrob p hp hf (Classical.choice (hZ (X0 x)).1)

include hY hZ hC0 hgood hbase in
theorem originalReducedPoint_parameter_value (i : Fin 3)
    (p : ULift (Fin (a.evaluation.count (some i)))) :
    ReducedPoint.originalReducedPoint j hsplit labels O l hTorsionQuotient a hlabels i p hgood hbase =
      originalCanonicalParameterValue j hsplit labels O l hTorsionQuotient a C0 X0 Yquotient Z0 QX hFrob i
        (CoordinatePointFactors.ReferencePresentation.originalProjection j hsplit labels O l hTorsionQuotient a i p)
        (CoordinatePointFactors.ReferencePresentation.originalIdentityFlag j hsplit labels O l hTorsionQuotient a i p) := by
  revert p
  refine Fin.cases ?_ ?_ i
  · exact originalReducedPoint_parameter_value_zero j hsplit labels O l hTorsionQuotient a hlabels
      C0 hC0 hgood hbase X0 Yquotient Z0 QX hY hFrob
  · intro i
    refine Fin.cases ?_ ?_ i
    · exact originalReducedPoint_parameter_value_one j hsplit labels O l hTorsionQuotient a hlabels
        C0 hC0 hgood hbase X0 Yquotient Z0 QX hY hZ hFrob
    · intro i
      refine Fin.cases ?_ (fun e => Fin.elim0 e) i
      exact originalReducedPoint_parameter_value_two j hsplit labels O l hTorsionQuotient a hlabels
        C0 hC0 hgood hbase X0 Yquotient Z0 QX hZ hFrob

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterEq.ReferencePoints

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterEq.ReferenceReducedCounts

/-! Exact multiplicities of all three original reduced neighbor families,
using the independent canonical X, Y, and Z quotients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCoordinates.X OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues.CoordinateCases
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedActive.ReferenceXPoint OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedPoint.ReferenceY OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedZ.ReferencePoint
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXYPoint OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXZPoint

variable (X0 : D.OrdinaryPoint → D.OrdinaryPoint)
  (Yquotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
  (Z0 : D.OrdinaryPoint → D.OrdinaryPoint)
  (QX : D.PrescribedOrdinaryQuotient x q (D.prescribedFullXKernel j iota hsplit labels O C0 x) (X0 x))
  (hY : ∀ y J, D.CanonicalOrdinaryQuotient y q
    (D.prescribedFullYKernel j iota hsplit labels O C0 y J) (Yquotient y J))
  (hZ : ∀ y, D.CanonicalOrdinaryQuotient y (q ^ 2)
    (D.prescribedFullZKernel j iota hsplit labels O C0 y) (Z0 y))
  (hFrob : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    D.prescribedFullXKernel j iota hsplit labels O C0 x T a ↔ D.relativeFrobeniusKernelCondition x T a)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterEq.ReferencePoints OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ThreeParameterCounts

def originalReducedMultiset (i : Fin 3) : Multiset D.GeometricPoint :=
  Finset.univ.val.map (fun p => ReducedPoint.originalReducedPoint j hsplit labels O l hTorsionQuotient a hlabels i p hgood hbase)

attribute [local irreducible] ReducedPoint.originalReducedPoint CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv
  IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor CoordinateSubspaces.originalCoordinateKernelParameters
  Canonical.ActiveCoordinates.X.canonicalXLineEquiv

include hY hZ hC0 in
theorem originalReducedMultiset_parameter_eq (i : Fin 3) :
    originalReducedMultiset j hsplit labels O l hTorsionQuotient a hlabels hgood hbase i =
      ThreeParameterCounts.originalLabeledParameters (fun i : Fin 3 => ULift (Fin (a.evaluation.count (some i))))
        (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a)
        (ReferencePoints.originalCanonicalParameterValue j hsplit labels O l hTorsionQuotient a C0 X0 Yquotient Z0 QX hFrob) i := by
  unfold originalReducedMultiset ThreeParameterCounts.originalLabeledParameters
  apply Multiset.map_congr rfl
  intro p _
  exact ReferencePoints.originalReducedPoint_parameter_value j hsplit labels O l hTorsionQuotient a hlabels C0 hC0 hgood hbase
    X0 Yquotient Z0 QX hY hZ hFrob i p

include hY hZ hC0 QX hFrob in
theorem originalReducedMultiset_counts :
    originalReducedMultiset j hsplit labels O l hTorsionQuotient a hlabels hgood hbase 0 =
      {(X0 x).val} + q • ((AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient x)).map Subtype.val) ∧
    originalReducedMultiset j hsplit labels O l hTorsionQuotient a hlabels hgood hbase 1 =
      ((AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient (X0 x))).map Subtype.val) + q ^ 2 • {(Z0 x).val} ∧
    originalReducedMultiset j hsplit labels O l hTorsionQuotient a hlabels hgood hbase 2 = {(Z0 (X0 x)).val} := by
  have h := Parameter.CanonicalValues.original_canonical_parameter_counts
    (fun i : Fin 3 => ULift (Fin (a.evaluation.count (some i))))
    (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a)
    (X0 x).val (Z0 x).val (Z0 (X0 x)).val
    (fun J => (Yquotient x J).val) (fun J => (Yquotient (X0 x) J).val)
    (CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv j hsplit labels O l hTorsionQuotient a)
    ((CoordinatePointFactors.ReferencePresentation.originalSpecialLineEquiv j hsplit labels O l hTorsionQuotient a).trans
      (Canonical.ActiveCoordinates.X.canonicalXLineEquiv j hsplit labels O C0 QX hFrob))
  have he := originalReducedMultiset_parameter_eq j hsplit labels O l hTorsionQuotient a hlabels
    C0 hC0 hgood hbase X0 Yquotient Z0 QX hY hZ hFrob
  have hy0 := AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport.Construction.etaleLineMultiset_map (Yquotient x)
    (Subtype.val : D.OrdinaryPoint → D.GeometricPoint)
  have hy1 := AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport.Construction.etaleLineMultiset_map (Yquotient (X0 x))
    (Subtype.val : D.OrdinaryPoint → D.GeometricPoint)
  refine ⟨(he 0).trans (h.1.trans ?_), (he 1).trans (h.2.1.trans ?_),
    (he 2).trans h.2.2⟩
  · exact congrArg (fun m => {(X0 x).val} + q • m) hy0.symm
  · exact congrArg (fun m => m + q ^ 2 • {(Z0 x).val}) hy1.symm

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterEq.ReferenceReducedCounts

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterEq.ReferenceIntrinsicReduction

/-! Package the constructed evaluation field, DVR, original full PEL
neighbors, and proved multiplicities into the native reduction result. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleLineMultisetTransport.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PointIsogeny.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Canonical.ActiveCoordinates.X OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.CanonicalValues.CoordinateCases
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedActive.ReferenceXPoint OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReferenceReducedPoint.ReferenceY OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedZ.ReferencePoint
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXYPoint OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ReducedXZPoint

variable (X0 : D.OrdinaryPoint → D.OrdinaryPoint)
  (Yquotient : D.OrdinaryPoint → AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q → D.OrdinaryPoint)
  (Z0 : D.OrdinaryPoint → D.OrdinaryPoint)
  (QX : D.PrescribedOrdinaryQuotient x q (D.prescribedFullXKernel j iota hsplit labels O C0 x) (X0 x))
  (hY : ∀ y J, D.CanonicalOrdinaryQuotient y q
    (D.prescribedFullYKernel j iota hsplit labels O C0 y J) (Yquotient y J))
  (hZ : ∀ y, D.CanonicalOrdinaryQuotient y (q ^ 2)
    (D.prescribedFullZKernel j iota hsplit labels O C0 y) (Z0 y))
  (hFrob : ∀ (T : Over D.integralGeometricBase.left)
    (a : T ⟶ (D.pointDatum x.val).data.polarized.abelian.scheme),
    D.prescribedFullXKernel j iota hsplit labels O C0 x T a ↔ D.relativeFrobeniusKernelCondition x T a)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterEq.ReferenceReducedCounts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

include a hlabels hgood QX hFrob hY hZ hC0 in
theorem nativeReductionResult_of_activeEvaluation :
    Intrinsic.ReductionSpecification.NativeReductionResult (L := L) j hsplit (Intrinsic.KernelLabels.nativeKernelLabels labels) 0 (Fin.cases false (O.compact x))
      hTorsionQuotient hbase X0 (fun y => AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction.etaleLineMultiset (Yquotient y)) Z0 x l := by
  refine ⟨a.evaluation, ?_⟩
  let := a.evaluation.scalarAlgebra R
  let := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  refine ⟨v, ⟨l.overEvaluationDVR v⟩,
    (fun i p => IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels i p hgood), ?_⟩
  exact ReferenceReducedCounts.originalReducedMultiset_counts j hsplit labels O l hTorsionQuotient a hlabels
    C0 hC0 hgood hbase X0 Yquotient Z0 QX hY hZ hFrob

end AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterEq.ReferenceIntrinsicReduction

end

end OAI
