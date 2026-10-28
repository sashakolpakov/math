import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinaryCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinaryCoordinateModel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedBlockSplitting

/-! # Evaluation DVR Ordinary Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates.Ordinary

noncomputable section

/-! Ordinary coordinates over an arbitrary evaluation DVR, constructed
from the original generic block splitting and the actual evaluated lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupOrdinaryCoordinates.Ordinary
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

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

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedBlockSplitting OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinaryCoordinates.Ordinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinaryCoordinateModel.Ordinary

def evaluationDVRActiveSplitting :=
  Intrinsic.EvaluatedBlockSplitting.nativeEvaluatedBlockSplitting j iota hsplit R F L l.polarized.abelian l.action
    v 1 (labels (0, false)) eA (Evaluated.LiftBlockIso.evaluatedLiftBlockIso j hsplit l v 1 (labels (0, false)))

def evaluationDVRIdentityCoordinates :=
  Lifted.OrdinaryCoordinates.Ordinary.liftedOrdinaryIdentityCoordinates (D := D) (R := v.carrier) (L := L) (x := x)
    j hsplit labels O (l.overEvaluationDVR v)
    (evaluationDVRActiveSplitting j hsplit labels l v eA)

def evaluationDVRIntegralSplit :=
  Lifted.OrdinaryCoordinates.Ordinary.liftedOrdinaryIntegralSplit (D := D) (R := v.carrier) (L := L) (x := x)
    j hsplit labels O (l.overEvaluationDVR v)
    (evaluationDVRActiveSplitting j hsplit labels l v eA)

def evaluationDVRCoordinateModel :=
  Lifted.OrdinaryCoordinateModel.Ordinary.liftedOrdinaryCoordinateModel (D := D) (R := v.carrier) (L := L) (x := x)
    j hsplit labels O (l.overEvaluationDVR v)
    (evaluationDVRActiveSplitting j hsplit labels l v eA)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates.Ordinary
