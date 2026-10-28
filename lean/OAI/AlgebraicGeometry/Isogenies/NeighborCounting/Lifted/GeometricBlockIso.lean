import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointDataSpecialization
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification

/-! # Geometric Block Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso

noncomputable section

/-! The actual geometric fiber of an original lifted block is the
original ordinary block at its moduli point, with the same inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OperatorSpecification.Construction
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison

def nativeActionBlockGroup {O : Type} [CommRing O] {S : Scheme} {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (n : ℕ) (a : O) : Grp (Over S) :=
  Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (ρ.map a))

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E (s + 1)}
  {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
  {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
  (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ))
  {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)

def liftedGeometricBlockGroupIso (n : ℕ) (v : Fin (s + 1)) :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).mapGrp.obj
      (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (l.action.map (j.projector iota hsplit n (labels (v, false)))))) ≅
    nativeActionBlockGroup (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action
      (q ^ n) (j.projector iota hsplit n (labels (v, false))) := by
  let t := Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso)
  let τ := labels (v, false)
  let e := l.geometricActionIso
  let PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * (s + 1)) P.polarizationType N
      (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) := l.polarized.pullback t
  let PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel (3 * (s + 1)) P.polarizationType N
      (Spec (.of (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q))) := (D.pointDatum x.val).data.polarized
  let ρA : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian := l.action.pullback t
  let ρB : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian := (D.pointDatum x.val).data.action
  let eA : PA.abelian.scheme ≅ PB.abelian.scheme := e.polarized.abelian
  have : IsMonHom eA.hom := e.polarized.abelianGroup
  exact Intrinsic.BlockBaseChange.nativeBlockBaseChangeGroupIso j iota hsplit l.polarized.abelian l.action t n τ ≪≫
    BlockSourceIso.blockSourceGroupIso (q ^ n) (ρA.map (j.projector iota hsplit n τ))
      (ρB.map (j.projector iota hsplit n τ)) eA (e.action (j.projector iota hsplit n τ))

def liftedGeometricOrdinarySplitting (O : D.OrdinaryKernelData j iota hsplit labels)
    (n : ℕ) (v : Fin (s + 1)) :
    AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q)
      ((Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).mapGrp.obj
        (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (l.action.map (j.projector iota hsplit n (labels (v, false)))))))
      q n (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights (O.compact x) v) (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights (O.compact x) v) :=
  liftedGeometricBlockGroupIso j hsplit labels l n v ≪≫
    Intrinsic.CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit (D.pointDatum x.val).data.polarized.abelian
      (D.pointDatum x.val).data.action n (labels (v, false)) ≪≫ O.splitting x n v

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
