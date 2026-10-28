import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizedIntegralQuotientKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.EvaluatedIntrinsicKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotientKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicNeighbors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntrinsicKernel

/-! # Intrinsic Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicKernelComparison.ReferenceIntrinsic

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

local instance finalNeighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
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
  CoordinateSubspaces.originalCoordinateKernelParameters Joint.KernelParameters.jointKernelParameters
  Evaluated.ActiveParameterFamily.SourceFamilies.evaluatedIntegralActiveSourceFamily

def originalIntegralGenericNormalizedKernelIdentity :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  NormalizedIntegralQuotientKernel.integralCanonicalQuotient_normalizedKernelIdentity
    j iota hsplit (l.overEvaluationDVR v).polarized (l.overEvaluationDVR v).action
    (l.overEvaluationDVR v).rosati
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) q _).mp D.polarizationPrimeToQ)
    (Intrinsic.KernelLabels.nativeKernelLabels labels) hlabels (HeckeExponents.neighborLevel i) (Nat.succ_le_succ (Nat.zero_le i.val))
    0 (Fin.cases false (O.compact x)) (IntegralActiveKernels.originalIntegralActiveKernel j hsplit labels O l hTorsionQuotient a i p)
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier a.evaluation.carrier)))

def originalIntegralKernelPullbackIdentity :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  NormalizedIntegralQuotientKernel.integralCanonicalQuotient_pulledKernelIdentity
    j iota hsplit (l.overEvaluationDVR v).polarized (l.overEvaluationDVR v).action
    (l.overEvaluationDVR v).rosati
    ((Nat.coprime_pow_right_iff (by decide : 0 < 2) q _).mp D.polarizationPrimeToQ)
    (Intrinsic.KernelLabels.nativeKernelLabels labels) hlabels (HeckeExponents.neighborLevel i) (Nat.succ_le_succ (Nat.zero_le i.val))
    0 (Fin.cases false (O.compact x)) (IntegralActiveKernels.originalIntegralActiveKernel j hsplit labels O l hTorsionQuotient a i p)
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier a.evaluation.carrier)))
    (Evaluated.SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := L) l v).hom

def originalConstructedEvaluatedKernelIdentity :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  EvaluatedIntrinsicKernel.ReferenceIntrinsicComparison.originalEvaluatedNativeKernelIdentity j hsplit labels O l hTorsionQuotient a i p
    (IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels i p hgood)

def originalNativeKernelIdentity := by
  have hk := (originalIntegralKernelPullbackIdentity j hsplit labels O l hTorsionQuotient a hlabels i p).down
  have hc := (originalConstructedEvaluatedKernelIdentity j hsplit labels O l hTorsionQuotient a hlabels i p hgood).down
  exact PLift.up (hk.trans hc)

theorem originalNativeKernel_eq :
    type_of% (originalNativeKernelIdentity j hsplit labels O l hTorsionQuotient a hlabels i p hgood).down :=
  (originalNativeKernelIdentity j hsplit labels O l hTorsionQuotient a hlabels i p hgood).down

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicKernelComparison.ReferenceIntrinsic
