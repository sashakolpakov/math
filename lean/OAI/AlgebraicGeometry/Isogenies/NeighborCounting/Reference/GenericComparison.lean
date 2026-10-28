import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateActiveComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.CoordinateKernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies

/-! # Generic Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericComparison

noncomputable section

section

/-! Prepare actual full-kernel transport and original-parameter comparison, retaining every original parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericActiveKernels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces.IntrinsicRationalMembership
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeBlockSplitting OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitKernelParameterComparison
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

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

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (w : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false (O.compact x)) i w)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) _
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false (O.compact x)) i w)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateActiveComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveAmbientData.ReferenceFamily
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.CoordinateKernelComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

attribute [local irreducible] CoordinateSubspaces.originalCoordinateKernelParameters
  Joint.KernelParameters.jointKernelParameters
  Evaluated.ActiveParameterFamily.SourceFamilies.evaluatedIntegralActiveSourceFamily
  Kernel.Base.fullKernel
  AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
  AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion

def originalCoordinateFullKernelTransport :=
  letI := a.evaluation.scalarAlgebra R
  letI : IsScalarTower R L a.evaluation.carrier := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  Evaluated.CoordinateKernelComparison.evaluatedCoordinateFullKernelComparison (F := L) (L := a.evaluation.carrier)
    j hsplit labels O l v a.blockIso

def originalCoordinateFullKernelImplication :=
  originalCoordinateFullKernelTransport j hsplit labels O l hTorsionQuotient a
    (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val
    (HeckeExponents.neighborLevel i) (Fin.cases false (O.compact x))
    (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice (l.genericPolarized (L := L)).abelian
      (O.compact x) (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l)
      hTorsionQuotient a.evaluation i p).val.subgroup

def originalMultiplierGenericKernelIdentity :=
  PLift.up ((originalCoordinateFullKernelImplication j hsplit labels O l hTorsionQuotient a i p).down
    (CoordinateActiveComparison.originalActualCoordinateActiveIdentity j hsplit labels O l hTorsionQuotient a i p).down)

def originalMultiplierGenericNormalizedIdentity := by
  have h := (originalMultiplierGenericKernelIdentity j hsplit labels O l hTorsionQuotient a i p).down
  dsimp (config := { instances := true }) only [Lifts.IntegralLift.actionData, PELModuli.IntegralModel.PEL.Has.PolarizedActionData.pullback,
    ActionBlockPairingIso.Polarized.canonicalActionBlockPairing] at h
  unfold Grp.ofHom Grp.homMk Grp.homMk' at h
  try dsimp (config := { instances := true }) only at h
  exact PLift.up h

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ParameterSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ChoiceFunctor
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation

omit [IsGalois ℚ E] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsFractionRing R L] in
theorem originalEvaluatedActiveChoice_eq :
    (Intrinsic.ReductionSpecification.evaluatedChoice (L := L) j hsplit (Intrinsic.KernelLabels.nativeKernelLabels labels) 0
      (Fin.cases false (O.compact x)) hTorsionQuotient l a.evaluation i p 0).val.subgroup =
    (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice (l.genericPolarized (L := L)).abelian
      (O.compact x) (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l)
      hTorsionQuotient a.evaluation i p).val.subgroup := by
  unfold Intrinsic.ReductionSpecification.evaluatedChoice Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice ParameterSubspaces.evaluatedTuple Intrinsic.ChoiceFunctor.nativeChoiceRepresentation
  rfl

def originalCompleteParameterKernelIdentity := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier))
  have h := congrArg (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
    (Grp.mk (l.genericPolarized (L := L)).abelian.scheme) (Over.mk f))
    (KernelComparison.originalCompleteKernel_eq j hsplit labels O l hTorsionQuotient a.evaluation i p).symm
  unfold Kernel.Models.multiplierFullKernel at h
  rw [originalEvaluatedActiveChoice_eq] at h
  unfold Intrinsic.ReductionSpecification.genericCanonicalPairing AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction.l45SourceBlockPairing Intrinsic.ParameterEnumeration.originalNeighborProjectors
    CMPointsHeckeEvaluation.l45NeighborProjectors AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors
    Lifts.IntegralLift.genericPolarized Lifts.IntegralLift.genericAction Lifts.IntegralLift.polarized Lifts.IntegralLift.action
    Intrinsic.ReductionSpecification.evaluatedBase at h
  try dsimp (config := { instances := true }) only at h
  exact PLift.up h

end

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericActiveKernels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveChoiceImage.Prime OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces.IntrinsicRationalMembership
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PrimeBlockSplitting OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitKernelParameterComparison
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

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

local instance finalNeighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

variable (a : ConstructedActiveEvaluation.LiftedActiveEvaluation (L := L) j hsplit labels O l hTorsionQuotient)

variable (i : Fin 3) (p : ULift (Fin (a.evaluation.count (some i))))

local instance finalPrimeNonzero : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance finalNeighborModule (w : Fin (s + 1)) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false (O.compact x)) i w)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) _
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false (O.compact x)) i w)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateActiveComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveAmbientData.ReferenceFamily
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.KernelComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.CoordinateKernelComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EmbeddedActiveFamilies OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

attribute [local irreducible] CoordinateSubspaces.originalCoordinateKernelParameters
  Joint.KernelParameters.jointKernelParameters
  Evaluated.ActiveParameterFamily.SourceFamilies.evaluatedIntegralActiveSourceFamily
  Kernel.Base.fullKernel
  AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
  AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion

def originalCompleteGenericKernelIdentity := by
  have h := (originalMultiplierGenericNormalizedIdentity j hsplit labels O l hTorsionQuotient a i p).down
  have k := (originalCompleteParameterKernelIdentity j hsplit labels O l hTorsionQuotient a i p).down
  exact PLift.up (h.trans k)

theorem originalCompleteGenericKernel_eq :
    type_of% (originalCompleteGenericKernelIdentity j hsplit labels O l hTorsionQuotient a i p).down :=
  (originalCompleteGenericKernelIdentity j hsplit labels O l hTorsionQuotient a i p).down

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericComparison
