import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockRank
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PointRank
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateKernel

/-! # Geometric Points -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricPoints

noncomputable section

/-! The point counts needed by the parameter enumeration
are derived for every geometric extension of the actual generic lift.
Finite etaleness comes from TorsionQuotient; rank comes from the ordinary special
fiber and the actual integral source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateKernel.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockRank OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.PointRank

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
  {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})

include O hTorsionQuotient in
omit [IsFractionRing R L] in
theorem liftedGeometricBlock_card (n : ℕ) (v : Fin (s + 1))
    (k : Type) [Field k] [IsAlgClosed k] (f : Spec (.of k) ⟶ Spec (.of L)) :
    Nat.card (Additive (Over.mk f ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n)
      ((l.genericAction (L := L)).map (j.projector iota hsplit n (labels (v, false)))))) =
        (q ^ n) ^ 3 := by
  let A := (l.genericPolarized (L := L)).abelian
  let p := (l.genericAction (L := L)).map (j.projector iota hsplit n (labels (v, false)))
  let G := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) p
  have hg := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock_finite_etale (q ^ n) p
    (AbelianScheme.IsogenyQuotient.Kernel.Assembly.Construction.torsion_finite_etale_from_TorsionQuotient (A := A.scheme) (𝟙 (Spec (.of L)))
      (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) hTorsionQuotient)
  let : IsFinite G.hom := hg.1
  let : Etale G.hom := hg.2
  let : Flat G.hom := inferInstance
  let : Etale ((Over.pullback f).obj G).hom :=
    inferInstanceAs (Etale (Limits.pullback.snd G.hom f))
  change Nat.card (Over.mk f ⟶ G) = _
  exact (Geometric.PointRank.geometricPoints_card_eq_rank G f).trans
    (BlockRank.generic_lift_nativeBlock_rank j hsplit labels O l n v (f (IsLocalRing.closedPoint k)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricPoints
