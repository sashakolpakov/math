import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointDataSpecialization

/-! # Lift Construction -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Starting with DVRLifting's actual smooth lift, construct the finite
evaluation field for its three IsogenyQuotient families and source q-torsion, the
complete evaluation DVR, and the base-changed lift of the same point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
variable (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
variable (active : Fin s) (multiplicative : Fin s → Bool) (h_TorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

section

variable {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

abbrev Lifts.IntegralLift.genericPolarized := l.polarized.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))

abbrev Lifts.IntegralLift.genericAction := l.action.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))

local instance Lifts.IntegralLift.heckeProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (Sum.inl v)))

def Lifts.IntegralLift.heckeEvaluation : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
    (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
      (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) labels) h_TorsionQuotient) :=
  CMPointsHeckeEvaluation.l45NativeHeckeEvaluation j iota hsplit (l.genericPolarized (L := L)).abelian
    (l.genericAction (L := L)) labels active multiplicative h_TorsionQuotient

def Lifts.IntegralLift.heckeEvaluationDVR :
    let d := l.heckeEvaluation (L := L) j hsplit labels active multiplicative h_TorsionQuotient
    letI := d.scalarAlgebra R
    EvaluationDVRLifts.EvaluationDVR R d.carrier := by
  letI : IsAlgClosed (IsLocalRing.ResidueField R) :=
    IsAlgClosed.of_ringEquiv (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q) _ residueIso
  exact (l.heckeEvaluation (L := L) j hsplit labels active multiplicative h_TorsionQuotient).integerDVR R

/-- The lift over the constructed evaluation ring specializes to the
same original moduli point, with its native polarization and marking. -/
def Lifts.IntegralLift.evaluatedHeckeLift :
    let d := l.heckeEvaluation (L := L) j hsplit labels active multiplicative h_TorsionQuotient
    letI := d.scalarAlgebra R
    let v := l.heckeEvaluationDVR (L := L) j hsplit labels active multiplicative h_TorsionQuotient
    Lifts.IntegralLift D v.carrier ((algebraMap R v.carrier).comp b)
      (residueIso.trans v.residueIso) x := by
  let d := l.heckeEvaluation (L := L) j hsplit labels active multiplicative h_TorsionQuotient
  letI := d.scalarAlgebra R
  exact l.overEvaluationDVR (l.heckeEvaluationDVR (L := L) j hsplit labels active multiplicative h_TorsionQuotient)

end

/-- DVRLifting and the native evaluation constructions produce the evaluated
lift from the original geometric point and arithmetic base. -/
def Evaluated.LiftConstruction.Lifts.constructedEvaluatedHeckeLift (hbase : Lifts.ResidueCompatible D R b residueIso) (x : D.GeometricPoint) :
    let l := Lifts.integralLift D R b residueIso hbase x
    let d := l.heckeEvaluation (L := L) j hsplit labels active multiplicative h_TorsionQuotient
    letI := d.scalarAlgebra R
    let v := l.heckeEvaluationDVR (L := L) j hsplit labels active multiplicative h_TorsionQuotient
    NeighborCounting.Lifts.IntegralLift D v.carrier ((algebraMap R v.carrier).comp b)
      (residueIso.trans v.residueIso) x :=
  (Lifts.integralLift D R b residueIso hbase x).evaluatedHeckeLift (L := L)
    j hsplit labels active multiplicative h_TorsionQuotient

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
