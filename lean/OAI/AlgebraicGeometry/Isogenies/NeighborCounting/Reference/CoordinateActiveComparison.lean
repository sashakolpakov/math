import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveParameterComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveAmbientData

/-! # Coordinate Active Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateActiveComparison

noncomputable section

/-! Expose the constructed integral active family at the unchanged original coordinate enumeration. -/

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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveParameterComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveParameterFamily.SourceFamilies OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveAmbientData
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveAmbientData OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CoordinateSubspaces

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.ActiveAmbientData.ReferenceFamily

attribute [local irreducible] Joint.KernelParameters.jointKernelParameters
  ActiveAmbientData.ReferenceFamily.originalIntegralActiveAmbientFamily

def originalCoordinateActiveIdentity := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap L a.evaluation.carrier))
  let F₀ := (Evaluated.ActiveChoiceImage.Prime.evaluatedPrimeActiveChoice (l.genericPolarized (L := L)).abelian
    (O.compact x) (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l) hTorsionQuotient a.evaluation i p).val.subgroup
  have h := ActiveParameterComparison.originalActiveParameter_eq j hsplit labels O l hTorsionQuotient a i p
  rw [ActiveAmbientData.ReferenceFamily.originalActiveAmbientComparison_family] at h
  have h' : ActiveAmbientData.ReferenceFamily.originalIntegralActiveAmbientFamily j hsplit labels O l hTorsionQuotient a
      (CoordinateSubspaces.originalCoordinateSubspaceEquiv j hsplit labels O l hTorsionQuotient a i p).val =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk (l.genericPolarized (L := L)).abelian.scheme)
        (Over.mk f) F₀ := by
    unfold CoordinateSubspaces.originalCoordinateSubspaceEquiv CoordinateSubspaces.originalCoordinateKernelParameters
      Intrinsic.CoordinateSubspaces.nativeCoordinateKernelParameters
    dsimp only at h
    exact h
  exact PLift.up h'

theorem originalCoordinateActive_eq :
    type_of% (originalCoordinateActiveIdentity j hsplit labels O l hTorsionQuotient a i p).down :=
  (originalCoordinateActiveIdentity j hsplit labels O l hTorsionQuotient a i p).down

def originalActualCoordinateActiveIdentity := by
  have h := originalCoordinateActive_eq j hsplit labels O l hTorsionQuotient a i p
  unfold ActiveAmbientData.ReferenceFamily.originalIntegralActiveAmbientFamily at h
  dsimp only at h
  exact PLift.up h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Reference.CoordinateActiveComparison
