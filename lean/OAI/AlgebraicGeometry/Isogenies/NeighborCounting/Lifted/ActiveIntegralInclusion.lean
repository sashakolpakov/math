import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.StandardResidueSplitting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockRank
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces

/-! # Active Integral Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.ActiveIntegralInclusion

noncomputable section

/-! The active block of the original integral lift has the actual
ordinary special splitting, finite local freeness, and rank q^3. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.StandardResidueSplitting OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock.Intrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockRank

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)
  {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

def liftedActiveIntegralInclusion :
    (OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels l).X ⟶ (ActionFamilyComparison.Family.actionFamily l.actionData).abelian.scheme :=
  AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ 1) (l.action.map (j.projector iota hsplit 1 (labels (0, false))))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.ActiveIntegralInclusion
