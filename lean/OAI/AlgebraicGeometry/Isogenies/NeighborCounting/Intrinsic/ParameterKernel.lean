import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedIntrinsicKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage

/-! # Parameter Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterKernel

noncomputable section

/-! Compose the complete-parameter kernel comparison with the native quotient
before specializing its evaluation field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactDetection.Neighbor
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockCoordinates OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.KernelDetection.Neighbor
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntrinsicKernel.Intrinsic
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime

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
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

variable (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q 0
    (Fin.cases false (O.compact x)) (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient))

variable (i : Fin 3) (a : ULift (Fin (d.count (some i))))

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (w : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false (O.compact x)) i w)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) _
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false (O.compact x)) i w)

local instance oppositeProjector_group (w : Fin (s + 1)) :
    IsMonHom (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) (s + 1) (KernelLabels.nativeKernelLabels labels) w) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (w, true)))

variable [Algebra R d.carrier] [IsScalarTower R L d.carrier]
  (v : EvaluationDVRLifts.EvaluationDVR R d.carrier)
  (Q : ReductionSpecification.EvaluatedNativeNeighbor j hsplit (KernelLabels.nativeKernelLabels labels) 0
    (Fin.cases false (O.compact x)) hTorsionQuotient l d v i a)

omit [IsGalois ℚ E] [IsFractionRing R L] [Algebra R d.carrier] [IsScalarTower R L d.carrier] in
theorem evaluatedActiveChoice_eq :
    (ReductionSpecification.evaluatedChoice (L := L) j hsplit (KernelLabels.nativeKernelLabels labels) 0
      (Fin.cases false (O.compact x)) hTorsionQuotient l d i a 0).val.subgroup =
    (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice (l.genericPolarized (L := L)).abelian
      (O.compact x) (ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l)
      hTorsionQuotient d i a).val.subgroup := by
  unfold ReductionSpecification.evaluatedChoice Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice Reference.ParameterSubspaces.evaluatedTuple ChoiceFunctor.nativeChoiceRepresentation
  rfl

attribute [local irreducible] Kernel.Base.fullKernel AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
  AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion
  AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.evaluatedChoiceEquiv
  HeckeEvaluation.nativeNeighborParameter HeckeEvaluation.neighborEvaluationSchemes

omit [IsFractionRing R L] [IsScalarTower R L d.carrier] in
private theorem completeParameterKernelBaseIdentity :
    let f := Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))
    type_of% ((congrArg (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
      (Grp.mk (l.genericPolarized (L := L)).abelian.scheme) (Over.mk f))
      (Reference.KernelComparison.originalCompleteKernel_eq j hsplit labels O l hTorsionQuotient d i a).symm).trans
      (Evaluated.IntrinsicKernel.Intrinsic.evaluatedNativeNeighbor_nativeKernel j hsplit (KernelLabels.nativeKernelLabels labels) 0
        (Fin.cases false (O.compact x)) hTorsionQuotient l d v i a Q).symm) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap L d.carrier))
  have hc := congrArg (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
    (Grp.mk (l.genericPolarized (L := L)).abelian.scheme) (Over.mk f))
    (Reference.KernelComparison.originalCompleteKernel_eq j hsplit labels O l hTorsionQuotient d i a).symm
  have hn := Evaluated.IntrinsicKernel.Intrinsic.evaluatedNativeNeighbor_nativeKernel j hsplit (KernelLabels.nativeKernelLabels labels) 0
    (Fin.cases false (O.compact x)) hTorsionQuotient l d v i a Q
  exact hc.trans hn.symm

def completeParameterNativeKernelIdentity := by
  have h := completeParameterKernelBaseIdentity j hsplit labels O l hTorsionQuotient d i a v Q
  unfold Kernel.Models.multiplierFullKernel at h
  rw [evaluatedActiveChoice_eq] at h
  unfold ReductionSpecification.genericCanonicalPairing AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction.l45SourceBlockPairing ParameterEnumeration.originalNeighborProjectors
    CMPointsHeckeEvaluation.l45NeighborProjectors AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors
    Lifts.IntegralLift.genericPolarized Lifts.IntegralLift.genericAction Lifts.IntegralLift.polarized Lifts.IntegralLift.action
    ReductionSpecification.evaluatedBase at h
  try dsimp (config := { instances := true }) only at h
  exact PLift.up h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterKernel
