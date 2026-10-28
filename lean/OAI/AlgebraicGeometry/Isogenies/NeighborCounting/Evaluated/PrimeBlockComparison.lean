import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointBaseChangeIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.LevelPointBaseChange

/-! # Prime Block Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison

noncomputable section

/-! The original literal q-block and the evaluated integral q¹-block
are compared by their actual group isomorphism. Its point map is the
same transport used to construct the integral active coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointBaseChangeIso

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L]
  [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (v : EvaluationDVRLifts.EvaluationDVR R L) (τ : Gal(E/ℚ))

def evaluatedPrimeBlockGroupIso :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).mapGrp.mapIso
    (Intrinsic.ActiveSubspaces.IntrinsicBlockLevelGroupIso.nativeBlockLevelGroupIso q (q ^ 1)
      ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
        (j.projector iota hsplit 1 τ)) (pow_one q).symm) ≪≫
    BlockPointComparison.evaluatedLiftGenericBlockGroupIso (F := F) j hsplit l v 1 τ

theorem evaluatedPrimeBlockGroupIso_points
    (a : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))) ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
        (j.projector iota hsplit 1 τ)))) :
    GroupPointBaseChange.baseChangedPointEquiv (Spec.map (CommRingCat.ofHom (algebraMap F L)))
      (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))) _ _
      (evaluatedPrimeBlockGroupIso (F := F) j hsplit l v τ) a.toMul =
    BlockPointComparison.evaluatedLiftBlockPointEquiv (F := F) j hsplit l v 1 τ
      (Intrinsic.ActiveSubspaces.nativeBlockPointLevelEquiv q (q ^ 1)
        ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
          (j.projector iota hsplit 1 τ)) (pow_one q).symm a).toMul := by
  have h := Intrinsic.LevelPointBaseChange.baseChangedPointEquiv_nativeLevel
    (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))) q (q ^ 1)
    ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
      (j.projector iota hsplit 1 τ)) (pow_one q).symm _
    (BlockPointComparison.evaluatedLiftGenericBlockGroupIso (F := F) j hsplit l v 1 τ) a
  exact h

theorem evaluatedActivePrimeBlockGroupIso_points
    (a : Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))) ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock q ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
        (j.projector iota hsplit 1 (labels (0, false)))))) :
    GroupPointBaseChange.baseChangedPointEquiv (Spec.map (CommRingCat.ofHom (algebraMap F L)))
      (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))) _ _
      (evaluatedPrimeBlockGroupIso (F := F) j hsplit l v (labels (0, false))) a.toMul =
        (ActiveCoordinateEquiv.evaluatedActivePointTransport (F := F) j hsplit labels l v a).toMul :=
  evaluatedPrimeBlockGroupIso_points j hsplit l v (labels (0, false)) a

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PrimeBlockComparison
