import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationActionIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso

/-! # Lift Block Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso

noncomputable section

/-! The actual evaluated integral lift has the base-changed original
native blocks, through its full source action isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)

def evaluatedLiftBlockGroupIso (n : ℕ) (τ : Gal(E/ℚ)) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R v.carrier)))).mapGrp.obj
      (Lifted.GeometricBlockIso.nativeActionBlockGroup l.polarized.abelian l.action (q ^ n) (j.projector iota hsplit n τ)) ≅
    Lifted.GeometricBlockIso.nativeActionBlockGroup (l.overEvaluationDVR v).polarized.abelian (l.overEvaluationDVR v).action
      (q ^ n) (j.projector iota hsplit n τ) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R v.carrier))
  let e := l.evaluationActionIso v
  let PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N (Spec (.of v.carrier)) :=
    l.polarized.pullback f
  let PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * s) P.polarizationType N (Spec (.of v.carrier)) :=
    (l.overEvaluationDVR v).polarized
  let ρA : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian := l.action.pullback f
  let ρB : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian := (l.overEvaluationDVR v).action
  let eA : PA.abelian.scheme ≅ PB.abelian.scheme := e.polarized.abelian
  have : IsMonHom eA.hom := e.polarized.abelianGroup
  exact Intrinsic.BlockBaseChange.nativeBlockBaseChangeGroupIso j iota hsplit l.polarized.abelian l.action f n τ ≪≫
    BlockSourceIso.blockSourceGroupIso (q ^ n) (ρA.map (j.projector iota hsplit n τ))
      (ρB.map (j.projector iota hsplit n τ)) eA (e.action (j.projector iota hsplit n τ))

def evaluatedLiftBlockIso (n : ℕ) (τ : Gal(E/ℚ)) :=
  (Grp.forget (Over (Spec (.of v.carrier)))).mapIso (evaluatedLiftBlockGroupIso j hsplit l v n τ)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso
