import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryBlockRank
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Ordinary Source Rank -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinarySourceRank.Ordinary

noncomputable section

/-! The supplied ordinary splittings determine rank three on every
original chosen block, at every level. The conclusion is stated on the
literal native block used by the generic subgroup-choice construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinaryBlockRank.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock.Intrinsic

theorem ordinary_heights_sum {s : ℕ} (c : Fin s → Bool) (v : Fin (s + 1)) :
    AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights c v + AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights c v = 3 := by
  refine Fin.cases rfl (fun w => ?_) v
  change (if c w then 3 else 0) + (if c w then 0 else 3) = 3
  cases c w <;> rfl

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  (O : D.OrdinaryKernelData j iota hsplit labels)

include O in
theorem ordinaryChosenBlock_rank (x : D.OrdinaryPoint) (n : ℕ) (v : Fin (s + 1))
    (z : Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) :
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n)
      ((D.pointDatum x.val).data.action.map (j.projector iota hsplit n (labels (v, false))))).hom.finrank z =
        (q ^ n) ^ 3 := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  exact (IntegralIntrinsicBlock.Intrinsic.integralNativeBlock_rank j iota hsplit (D.pointDatum x.val).data.polarized
    (D.pointDatum x.val).data.action n (labels (v, false)) z).trans
      (OrdinaryBlockRank.Ordinary.ordinaryBlock_rank_three (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) q n (O.splitting x n v)
        (ordinary_heights_sum (O.compact x) v) z)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinarySourceRank.Ordinary
