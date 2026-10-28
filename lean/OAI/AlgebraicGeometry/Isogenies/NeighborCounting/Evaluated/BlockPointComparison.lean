import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso

/-! # Block Point Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison

noncomputable section

/-! Compare original evaluation-field block points to the points of
the actual evaluated integral lift, through the constructed group isos. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupPointBaseChange
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockGroupComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x) (v : EvaluationDVRLifts.EvaluationDVR R L)
  (n : ℕ) (τ : Gal(E/ℚ))

def evaluatedLiftGenericBlockGroupIso :=
  BlockGroupComparison.evaluatedNativeBlockGroupIso R F L j iota hsplit l.polarized.abelian l.action v n τ
    (LiftBlockIso.evaluatedLiftBlockGroupIso j hsplit l v n τ)

def evaluatedLiftBlockPointEquiv :=
  GroupPointBaseChange.baseChangedPointEquiv (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    (Spec.map (CommRingCat.ofHom (algebraMap v.carrier L))) _ _
    (evaluatedLiftGenericBlockGroupIso (F := F) j hsplit l v n τ)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison
