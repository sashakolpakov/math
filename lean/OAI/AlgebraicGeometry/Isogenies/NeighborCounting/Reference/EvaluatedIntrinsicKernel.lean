import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotientKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicNeighbors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterKernel

/-! # Evaluated Intrinsic Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.EvaluatedIntrinsicKernel.ReferenceIntrinsicComparison

noncomputable section

/-! Compare the genuine generic kernels of the original integral
quotient and the independently constructed positive evaluated neighbor.
The complete-kernel identity supplies every compact and opposite block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotientKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicNeighbors.ReferenceIntrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntrinsicKernel.Intrinsic
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

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

attribute [local irreducible] Kernel.Base.fullKernel AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
  AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion
  AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.evaluatedChoiceEquiv
  Intrinsic.HeckeEvaluation.nativeNeighborParameter
  Intrinsic.HeckeEvaluation.neighborEvaluationSchemes
  Intrinsic.HeckeEvaluation.neighborChoiceFunctor
  CoordinateSubspaces.originalCoordinateKernelParameters Joint.KernelParameters.jointKernelParameters

def originalNativeParameterKernelIdentity
    (Q : letI := a.evaluation.scalarAlgebra R
      Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor j hsplit (Intrinsic.KernelLabels.nativeKernelLabels labels) 0
        (Fin.cases false (O.compact x)) hTorsionQuotient l a.evaluation
        (ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a) i p) :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  Intrinsic.ParameterKernel.completeParameterNativeKernelIdentity
    j hsplit labels O l hTorsionQuotient a.evaluation i p
    (ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a) Q

def originalEvaluatedNativeKernelIdentity
    (Q : letI := a.evaluation.scalarAlgebra R
      Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor j hsplit (Intrinsic.KernelLabels.nativeKernelLabels labels) 0
        (Fin.cases false (O.compact x)) hTorsionQuotient l a.evaluation
        (ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a) i p) := by
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  have hc := (GenericComparison.originalMultiplierGenericNormalizedIdentity
    j hsplit labels O l hTorsionQuotient a i p).down
  have hn := (originalNativeParameterKernelIdentity j hsplit labels O l hTorsionQuotient a i p Q).down
  exact PLift.up (hc.trans hn)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.EvaluatedIntrinsicKernel.ReferenceIntrinsicComparison
