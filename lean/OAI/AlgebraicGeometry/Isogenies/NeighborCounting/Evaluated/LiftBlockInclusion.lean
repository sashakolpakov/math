import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockSourceInclusion

/-! # Lift Block Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockInclusion

noncomputable section

/-! The actual evaluated integral lift comparison commutes with each original torsion-block inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockSourceInclusion

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

theorem evaluatedLiftBlockGroupIso_inclusion (n : ℕ) (τ : Gal(E/ℚ)) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R v.carrier))
    let e := l.evaluationActionIso v
    (LiftBlockIso.evaluatedLiftBlockGroupIso j hsplit l v n τ).hom.hom.hom ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) ((l.overEvaluationDVR v).action.map (j.projector iota hsplit n τ)) =
    (Over.pullback f).map (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (l.action.map (j.projector iota hsplit n τ))) ≫
      e.polarized.abelian.hom := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R v.carrier))
  let e := l.evaluationActionIso v
  let eA : (l.polarized.abelian.pullback f).scheme ≅ (l.overEvaluationDVR v).polarized.abelian.scheme :=
    e.polarized.abelian
  have : IsMonHom eA.hom := e.polarized.abelianGroup
  exact Intrinsic.BlockSourceInclusion.nativeBlockSourceIso_inclusion j iota hsplit l.polarized.abelian l.action
    (l.overEvaluationDVR v).polarized.abelian (l.overEvaluationDVR v).action f eA n τ
    (e.action (j.projector iota hsplit n τ))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockInclusion
