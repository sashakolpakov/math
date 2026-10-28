import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicKernelComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelSourceComparison

/-! # Generic Same Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericSameKernel

noncomputable section

/-! The genuine positive generic neighbor and the actual original
integral quotient have the same complete kernel on the generic fiber.
Every source and target PEL comparison is constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralActiveKernels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntegralQuotientKernel OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicNeighbors.ReferenceIntrinsic
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.IntrinsicKernelComparison.ReferenceIntrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelSourceComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntrinsicIntegralIsogeny.Intrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELSourceIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.SourceGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

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

def originalGenericPELBetweenModels :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  Evaluated.IntrinsicIntegralIsogeny.Intrinsic.evaluatedNativeIntegralIsogeny j hsplit (Intrinsic.KernelLabels.nativeKernelLabels labels) 0
    (Fin.cases false (O.compact x)) hTorsionQuotient l a.evaluation v i p
    (IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels i p hgood)

attribute [local irreducible] Kernel.Base.fullKernel AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter
  AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter.restrict AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion
  CoordinateSubspaces.originalCoordinateKernelParameters Joint.KernelParameters.jointKernelParameters
  Evaluated.ActiveParameterFamily.SourceFamilies.evaluatedIntegralActiveSourceFamily

def originalGenericPELHomIdentity :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let Q := IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels i p hgood
  PLift.up (Evaluated.IntrinsicIntegralIsogeny.Intrinsic.evaluatedNativeIntegralIsogeny_hom j hsplit (Intrinsic.KernelLabels.nativeKernelLabels labels) 0
    (Fin.cases false (O.compact x)) hTorsionQuotient l a.evaluation v i p Q)

def originalGenericSameKernelIdentity := by
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  let Q := IntrinsicNeighbors.ReferenceIntrinsic.originalNativeNeighbor j hsplit labels O l hTorsionQuotient a hlabels i p hgood
  let p₀ := IntegralQuotientKernel.originalIntegralGenericIsogeny j hsplit labels O l hTorsionQuotient a hlabels i p
  let e := Evaluated.PELSourceIso.evaluatedGenericSourceFamilyIso (F := L) l v
  let g := originalGenericPELBetweenModels j hsplit labels O l hTorsionQuotient a hlabels i p hgood
  exact PLift.up (@Intrinsic.KernelSourceComparison.sameKernel_of_sourceComparison_eq _ _ _ _ _ _ _ p₀ Q.quotient.isogeny e.abelian
    Q.target.genericFamilyIso.abelian.symm
    (by exact Q.target.genericFamilyIso.symm.abelianGroup) g.isogeny
    (Evaluated.SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := L) l v).hom.hom.hom
    (by exact (Evaluated.SourceGroupIso.evaluatedLiftGenericSourceGroupIso (F := L) l v).hom.hom.isMonHom_hom)
    (Evaluated.PELSourceIso.evaluatedGenericSourceFamilyIso_hom (F := L) l v)
    (IntrinsicKernelComparison.ReferenceIntrinsic.originalNativeKernel_eq j hsplit labels O l hTorsionQuotient a hlabels i p hgood)
    (originalGenericPELHomIdentity j hsplit labels O l hTorsionQuotient a hlabels i p hgood).down)

theorem originalGenericSameKernel :
    type_of% (originalGenericSameKernelIdentity j hsplit labels O l hTorsionQuotient a hlabels i p hgood).down :=
  (originalGenericSameKernelIdentity j hsplit labels O l hTorsionQuotient a hlabels i p hgood).down

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.GenericSameKernel
