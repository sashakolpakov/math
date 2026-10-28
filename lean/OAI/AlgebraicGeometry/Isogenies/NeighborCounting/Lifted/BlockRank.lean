import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinarySourceRank
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockRankTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointDataSpecialization
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftConstruction

/-! # Block Rank -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockRank

noncomputable section

/-! The original integral lift and its generic fiber have rank-three
chosen blocks. Rank constancy, actual source specialization, and native
block base change discharge the point-count input to enumeration. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OrdinarySourceRank.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock.Intrinsic OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockRankTransport

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

include O in
theorem integral_lift_nativeBlock_rank (n : ℕ) (v : Fin (s + 1)) (z : Spec (.of R)) :
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (l.action.map (j.projector iota hsplit n (labels (v, false))))).hom.finrank z =
      (q ^ n) ^ 3 := by
  let τ := labels (v, false)
  let t := Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso)
  let z0 : Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)) := IsLocalRing.closedPoint (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
  let G := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (l.action.map (j.projector iota hsplit n τ))
  obtain ⟨hf, hflat, hfp⟩ := IntegralIntrinsicBlock.Intrinsic.integralNativeBlock_finiteLocallyFree j iota hsplit l.polarized l.action n τ
  let : IsFinite G.hom := hf
  let : Flat G.hom := hflat
  let : LocallyOfFinitePresentation G.hom := hfp
  let e := l.geometricActionIso
  let PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * (s + 1)) P.polarizationType N
      (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) := l.polarized.pullback t
  let PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * (s + 1)) P.polarizationType N
      (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) := (D.pointDatum x.val).data.polarized
  let ρA : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian := l.action.pullback t
  let ρB : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian := (D.pointDatum x.val).data.action
  let eA : PA.abelian.scheme ≅ PB.abelian.scheme := e.polarized.abelian
  have : IsMonHom eA.hom := e.polarized.abelianGroup
  calc
    G.hom.finrank z = G.hom.finrank (t z0) :=
      G.hom.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace _ _
    _ = (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) ((l.action.pullback t).map (j.projector iota hsplit n τ))).hom.finrank z0 :=
      (Intrinsic.BlockRankTransport.nativeBlock_baseChange_rank j iota hsplit l.polarized l.action n τ t z0).symm
    _ = (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n)
        ((D.pointDatum x.val).data.action.map (j.projector iota hsplit n τ))).hom.finrank z0 :=
      Intrinsic.BlockRankTransport.nativeBlock_sourceIso_rank j iota hsplit PA ρA n τ PB ρB eA e.action z0
    _ = (q ^ n) ^ 3 := OrdinarySourceRank.Ordinary.ordinaryChosenBlock_rank D j hsplit labels O x n v z0

variable {L : Type} [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]

include O in
omit [CharZero L] [IsFractionRing R L] in
theorem generic_lift_nativeBlock_rank (n : ℕ) (v : Fin (s + 1)) (z : Spec (.of L)) :
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n)
      ((l.genericAction (L := L)).map (j.projector iota hsplit n (labels (v, false))))).hom.finrank z =
        (q ^ n) ^ 3 :=
  (Intrinsic.BlockRankTransport.nativeBlock_baseChange_rank j iota hsplit l.polarized l.action n (labels (v, false))
    (Spec.map (CommRingCat.ofHom (algebraMap R L))) z).trans
      (integral_lift_nativeBlock_rank j hsplit labels O l n v _)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.BlockRank
