import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces

/-! # Active Coordinate Equiv -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv

noncomputable section

/-! Give the original evaluation-field q-block its constructed linear
coordinates using the actual evaluated ordinary lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.BlockPointComparison
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveSubspaces OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces

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
  {R F L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Field L] [Algebra R F] [Algebra F L] [Algebra R L]
  [IsScalarTower R F L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (v : EvaluationDVRLifts.EvaluationDVR R L)
  {I : Type} [Finite I]
  (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).obj
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1) (((l.action).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
          (j.projector iota hsplit 1 (labels (0, false))))))

/-! Package each large equivalence before composing it with the next one.
This keeps the coordinate construction and the two base-change transports as
separate mathematical steps. -/

def evaluatedActivePointTransportComparison :=
  PLift.up
    ((Intrinsic.ActiveSubspaces.nativeBlockPointLevelEquiv
      (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F L))))
      q (q ^ 1) ((l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map
        (j.projector iota hsplit 1 (labels (0, false)))) (pow_one q).symm).trans
      (BlockPointComparison.evaluatedLiftBlockPointEquiv
        (F := F) j hsplit l v 1 (labels (0, false))).toAdditive)

abbrev evaluatedActivePointTransport :=
  (evaluatedActivePointTransportComparison (F := F) j hsplit labels l v).down

def evaluatedActiveCoordinateComparison :=
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel j hsplit labels O l v eA
  let hk := Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock_killed j hsplit labels (l.overEvaluationDVR v) (Sections.Lifts.genericTest v.carrier L)
  letI := GenericPointCoordinates.Lifts.genericPointModule v.carrier L q (Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock j hsplit labels (l.overEvaluationDVR v)).X hk
  PLift.up
    ((OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.linearCoordinates
      (R := v.carrier) (L := L) (q := q)
      (A := Lifted.OrdinarySplitting.Ordinary.liftedActiveBlock
        j hsplit labels (l.overEvaluationDVR v)) C hk).toAddEquiv)

abbrev evaluatedActiveCoordinateAddEquiv :=
  (evaluatedActiveCoordinateComparison j hsplit labels O l v eA).down

def evaluatedActiveLevelOnePointComparison :=
  PLift.up
    ((BlockPointComparison.evaluatedLiftBlockPointEquiv
      (F := F) j hsplit l v 1 (labels (0, false))).toAdditive.trans
      (evaluatedActiveCoordinateAddEquiv j hsplit labels O l v eA))

abbrev evaluatedActiveLevelOnePointAddEquiv :=
  (evaluatedActiveLevelOnePointComparison (F := F) j hsplit labels O l v eA).down

def evaluatedActivePointComparison :=
  PLift.up
    ((evaluatedActivePointTransport
      (F := F) j hsplit labels l v).trans
      (evaluatedActiveCoordinateAddEquiv j hsplit labels O l v eA))

abbrev evaluatedActivePointAddEquiv :=
  (evaluatedActivePointComparison (F := F) j hsplit labels O l v eA).down

def evaluatedActivePointLinearComparison :=
  PLift.up
    (ActiveTypedSubspaces.zmodLinearEquiv q
      (evaluatedActivePointAddEquiv
        (F := F) j hsplit labels O l v eA))

abbrev evaluatedActivePointLinearEquiv :=
  (evaluatedActivePointLinearComparison (F := F) j hsplit labels O l v eA).down

def evaluatedActiveIntegralKernel (J : Submodule (ZMod q) ((Fin 2 → ZMod q) × ZMod q)) :
    Kernel.Properties.FiniteFlatKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
      ((l.overEvaluationDVR v).action.map (j.projector iota hsplit 1 (labels (0, false))))) :=
  let C := EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel j hsplit labels O l v eA
  OrdinaryCoordinateLinear.Lifts.OrdinaryCoordinateModel.finiteFlatKernel (R := v.carrier) (L := L) (q := q) (A := _) C J

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ActiveCoordinateEquiv
