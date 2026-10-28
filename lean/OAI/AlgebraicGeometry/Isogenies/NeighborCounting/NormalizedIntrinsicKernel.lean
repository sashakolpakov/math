import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntrinsicKernel

/-! # Normalized Intrinsic Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedIntrinsicKernel.Intrinsic

noncomputable section

/-! Normalize the actual evaluated neighbor kernel before specialization to
the original parameter field. All complete kernel and PEL data are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntrinsicKernel.Intrinsic

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
variable {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
variable (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ)) (active : Fin s) (multiplicative : Fin s → Bool)
variable (h_TorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput) {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (i : Fin 3) (v : Fin s) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents active multiplicative i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents active multiplicative i v) (HeckeExponents.neighborExponents_bound active multiplicative i v)

local instance chosenProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (.inl v)))

local instance oppositeProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) s labels v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (.inr v)))

variable (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
    (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels) h_TorsionQuotient))

variable [Algebra R d.carrier] [IsScalarTower R L d.carrier]
variable (v : EvaluationDVRLifts.EvaluationDVR R d.carrier)
  (i : Fin 3) (a : ULift (Fin (d.count (some i))))
  (Q : Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d v i a)

attribute [local irreducible] AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
  AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.evaluatedChoiceEquiv Intrinsic.HeckeEvaluation.nativeNeighborParameter
  Intrinsic.HeckeEvaluation.neighborEvaluationSchemes Intrinsic.HeckeEvaluation.neighborChoiceFunctor AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing
  AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion

def evaluatedNativeNeighbor_normalizedKernelIdentity := by
  have h := Evaluated.IntrinsicKernel.Intrinsic.evaluatedNativeNeighbor_nativeKernel j hsplit labels active multiplicative h_TorsionQuotient l d v i a Q
  unfold Intrinsic.ReductionSpecification.evaluatedCompleteKernel at h
  delta Intrinsic.ReductionSpecification.genericCanonicalPairing Intrinsic.ReductionSpecification.genericSource Intrinsic.ReductionSpecification.evaluatedBase
    AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction.l45SourceBlockPairing CMPointsHeckeEvaluation.l45NeighborProjectors AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors
    Lifts.IntegralLift.genericPolarized Lifts.IntegralLift.genericAction Lifts.IntegralLift.polarized Lifts.IntegralLift.action
    Lifts.IntegralLift.actionData PELModuli.IntegralModel.PEL.Has.PolarizedActionData.pullback
    Intrinsic.ReductionSpecification.neighborModule Evaluated.IntrinsicKernel.Intrinsic.neighborModule at h
  exact PLift.up h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedIntrinsicKernel.Intrinsic
