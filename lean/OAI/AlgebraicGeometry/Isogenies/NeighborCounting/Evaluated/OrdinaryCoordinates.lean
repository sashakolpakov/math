import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedOrdinaryCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupOrdinaryCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates

/-! # Ordinary Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.OrdinaryCoordinates.Ordinary

noncomputable section

/-! The original evaluated source has a constructed integral ordinary
product and a generic identity-line coordinate. Every geometric, rank,
torsion and splitting input comes from the original lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedOrdinaryCoordinates.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupOrdinaryCoordinates.Ordinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVROrdinaryCoordinates.Ordinary
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
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
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
  {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

variable (a : ConstructedActiveEvaluation.LiftedActiveEvaluation (L := L) j hsplit labels O l hTorsionQuotient)

def evaluatedActiveIdentityCoordinates :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRIdentityCoordinates (F := L) j hsplit labels O l
    (ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a) a.blockIso

def evaluatedActiveIntegralSplit :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRIntegralSplit (F := L) j hsplit labels O l
    (ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a) a.blockIso

def evaluatedActiveCoordinateModel :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  EvaluationDVROrdinaryCoordinates.Ordinary.evaluationDVRCoordinateModel (F := L) j hsplit labels O l
    (ConstructedActiveEvaluation.activeEvaluationDVR j hsplit labels O l hTorsionQuotient a) a.blockIso

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.OrdinaryCoordinates.Ordinary
