import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveBlock
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedBlockSplitting

/-! # Constructed Active Evaluation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation

noncomputable section

/-! Construct the original common evaluation field, its actual DVR,
the same-point evaluated lift, and the generic splitting of that lift's
active block. No splitting or evaluated source is a premise. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ParameterEnumeration OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveBlock.Evaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifted.OrdinarySplitting.Ordinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftBlockIso OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluatedBlockSplitting

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
  {x : D.OrdinaryPoint} (l : Lifts.IntegralLift D R b residueIso x.val)
  (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance neighborProjector_group (i : Fin 3) (v : Fin (s + 1)) :
    IsMonHom (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (v, false)))

abbrev LiftedActiveEvaluation :=
  ActiveBlock.Evaluation.ActiveBlockEvaluation (l.genericPolarized (L := L)).abelian q 0
    (Fin.cases false (O.compact x)) (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l)
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l 0 0) hTorsionQuotient

def constructActiveEvaluation : LiftedActiveEvaluation (L := L) j hsplit labels O l hTorsionQuotient :=
  ActiveBlock.Evaluation.activeBlockEvaluation (l.genericPolarized (L := L)).abelian q 0
    (Fin.cases false (O.compact x)) (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l)
    (Intrinsic.ParameterEnumeration.originalNeighborProjectors (L := L) j hsplit labels l 0 0) hTorsionQuotient

variable (a : LiftedActiveEvaluation (L := L) j hsplit labels O l hTorsionQuotient)

def activeEvaluationDVR :
    letI := a.evaluation.scalarAlgebra R
    EvaluationDVRLifts.EvaluationDVR R a.evaluation.carrier := by
  let : IsAlgClosed (IsLocalRing.ResidueField R) :=
    IsAlgClosed.of_ringEquiv (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) _ residueIso
  exact a.evaluation.integerDVR R

def activeEvaluationLift :
    letI := a.evaluation.scalarAlgebra R
    let v := activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
    Lifts.IntegralLift D v.carrier ((algebraMap R v.carrier).comp b)
      (residueIso.trans v.residueIso) x.val := by
  let := a.evaluation.scalarAlgebra R
  exact l.overEvaluationDVR (activeEvaluationDVR j hsplit labels O l hTorsionQuotient a)

def activeEvaluatedBlockSplitting :=
  letI := a.evaluation.scalarAlgebra R
  letI := a.evaluation.scalarTower R
  let v := activeEvaluationDVR j hsplit labels O l hTorsionQuotient a
  Intrinsic.EvaluatedBlockSplitting.nativeEvaluatedBlockSplitting j iota hsplit R L a.evaluation.carrier l.polarized.abelian l.action
    v 1 (labels (0, false)) a.blockIso (Evaluated.LiftBlockIso.evaluatedLiftBlockIso j hsplit l v 1 (labels (0, false)))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedActiveEvaluation
