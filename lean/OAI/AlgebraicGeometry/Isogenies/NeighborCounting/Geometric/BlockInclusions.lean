import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.SourceAction
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BaseChangeSourceInclusion

/-! # Block Inclusions -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockInclusions

noncomputable section

/-! The geometric block comparison retains the actual inclusion into
the source PEL point. This connects the integral subgroup presentations
to the independently prescribed ordinary block coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.GeometricBlockIso
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison

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

theorem geometricFamilyIso_hom :
    l.geometricFamilyIso.abelian.hom = l.geometricActionIso.polarized.abelian.hom := by
  change (𝟙 _) ≫ l.geometricActionIso.polarized.abelian.hom = _
  exact Category.id_comp _

theorem liftedGeometricBlockGroupIso_inclusion (n : ℕ) (v : Fin (s + 1)) :
    (Lifted.GeometricBlockIso.liftedGeometricBlockGroupIso j hsplit labels l n v).hom.hom.hom ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n)
        ((D.pointDatum x.val).data.action.map (j.projector iota hsplit n (labels (v, false)))) =
      (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (l.action.map (j.projector iota hsplit n (labels (v, false))))) ≫
        l.geometricActionIso.polarized.abelian.hom := by
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
  exact BaseChangeSourceInclusion.Block.composedBlock_inclusion j iota hsplit
    l.polarized.abelian l.action PB.abelian ρB t n τ eA (hegroup := e.polarized.abelianGroup)
    (e.action (j.projector iota hsplit n τ))

theorem liftedGeometricBlockGroupIso_point_inclusion (n : ℕ) (v : Fin (s + 1)) :
    (Lifted.GeometricBlockIso.liftedGeometricBlockGroupIso j hsplit labels l n v).hom.hom.hom ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n)
        ((D.pointDatum x.val).data.action.map (j.projector iota hsplit n (labels (v, false)))) =
      (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (l.action.map (j.projector iota hsplit n (labels (v, false))))) ≫
        l.geometricFamilyIso.abelian.hom :=
  (liftedGeometricBlockGroupIso_inclusion j hsplit labels l n v).trans
    (congrArg (fun f => (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (l.action.map (j.projector iota hsplit n (labels (v, false))))) ≫ f)
      (geometricFamilyIso_hom l).symm)

def liftedGeometricOriginalBlockIso (n : ℕ) (v : Fin (s + 1)) :
    (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).mapGrp.obj
      (Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (l.action.map (j.projector iota hsplit n (labels (v, false)))))) ≅
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit (D.pointDatum x.val).data.polarized.abelian
        (D.pointDatum x.val).data.action n (labels (v, false))).toGrp :=
  Lifted.GeometricBlockIso.liftedGeometricBlockGroupIso j hsplit labels l n v ≪≫
    Intrinsic.CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit (D.pointDatum x.val).data.polarized.abelian
      (D.pointDatum x.val).data.action n (labels (v, false))

def originalBlockInclusion (n : ℕ) (v : Fin (s + 1)) :=
  (liftedGeometricOriginalBlockIso j hsplit labels l n v).hom.hom.hom ≫
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
      (D.pointDatum x.val).data.action n (labels (v, false))

def originalSourceInclusion (n : ℕ) (v : Fin (s + 1)) :=
  (Over.pullback (Evaluated.Quotients.Lifts.geometricClosedBase (residueIso := residueIso))).map
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (l.action.map (j.projector iota hsplit n (labels (v, false))))) ≫
    l.geometricFamilyIso.abelian.hom

theorem liftedGeometricOriginalBlockIso_inclusion (n : ℕ) (v : Fin (s + 1)) :
    originalBlockInclusion j hsplit labels l n v =
      originalSourceInclusion j hsplit labels l n v := by
  let f := (Lifted.GeometricBlockIso.liftedGeometricBlockGroupIso j hsplit labels l n v).hom.hom.hom
  let g := (Intrinsic.CMPointsBlockComparison.nativeCMPointsBlockGroupIso j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action n (labels (v, false))).hom.hom.hom
  let k := AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (D.pointDatum x.val).data.polarized.abelian
    (D.pointDatum x.val).data.action n (labels (v, false))
  have hg := Intrinsic.CMPointsBlockComparison.nativeCMPointsBlockGroupIso_inclusion j iota hsplit
    (D.pointDatum x.val).data.polarized.abelian (D.pointDatum x.val).data.action n (labels (v, false))
  have hout := (Category.assoc f g k).trans ((congrArg (fun u => f ≫ u) hg).trans
    (liftedGeometricBlockGroupIso_point_inclusion j hsplit labels l n v))
  exact hout

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockInclusions
