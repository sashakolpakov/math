import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricPoints
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedBlockCoordinates

/-! # Block Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockCoordinates

noncomputable section

/-! Construct coordinates of every actual geometric chosen block of
the original generic lift. The ordinary source supplies its rank, TorsionQuotient
supplies division, and the integral action is preserved exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricPoints OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedBlockCoordinates

variable {E K : Type} [Field E] [NumberField E] [aE : Algebra ℚ E] [IsGalois ℚ E]
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
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

def liftedNativeBlockCoordinates (n : ℕ) (v : Fin (s + 1))
    (k : Type) [Field k] [IsAlgClosed k] (f : Spec (.of k) ⟶ Spec (.of L)) :
    Additive (Over.mk f ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n)
      ((l.genericAction (L := L)).map (j.projector iota hsplit n (labels (v, false))))) ≃+
        (Fin 3 → ZMod (q ^ n)) := by
  cases Subsingleton.elim aE (DivisionRing.toRatAlgebra : Algebra ℚ E)
  exact PolarizedBlockCoordinates.polarizedBlockCoordinates j iota hsplit (l.genericPolarized (L := L))
    (l.genericAction (L := L)) (labels (v, false)) k f
    ((GeometricPoints.liftedGeometricBlock_card j hsplit labels O l hTorsionQuotient 1 v k f).trans
      (by rw [pow_one])) n

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockCoordinates
