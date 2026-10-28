import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily

/-! # CM Points Hecke Evaluation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation

noncomputable section

/-! Use the literal CMPoints arithmetic projector lifts in the three IsogenyQuotient
parameter families. Their joint splitting field and complete evaluation
ring are constructed from the native abelian source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation

variable {E K L : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} [Field L] [CharZero L]
variable {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {d s : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of L)))
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
variable (active : Fin s) (multiplicative : Fin s → Bool) (h_TorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

abbrev l45NeighborProjectors (i : Fin 3) : Fin s → (A.scheme ⟶ A.scheme) :=
  AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ (HeckeExponents.neighborLevel i) s labels

def l45NativeHeckeEvaluation : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
    (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes A q active multiplicative
      (l45NeighborProjectors j iota hsplit A σ labels) h_TorsionQuotient) :=
  Intrinsic.HeckeEvaluation.nativeHeckeEvaluation A q active multiplicative
    (l45NeighborProjectors j iota hsplit A σ labels) h_TorsionQuotient

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Algebra R L] [IsFractionRing R L]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsAlgClosed (IsLocalRing.ResidueField R)]

/-- The same constructed complete DVR serves the three native parameter
families and the source torsion, including any required ramification. -/
def l45HeckeEvaluationDVR :
    let d := l45NativeHeckeEvaluation j iota hsplit A σ labels active multiplicative h_TorsionQuotient
    letI := d.scalarAlgebra R
    EvaluationDVRLifts.EvaluationDVR R d.carrier :=
  (l45NativeHeckeEvaluation j iota hsplit A σ labels active multiplicative h_TorsionQuotient).integerDVR R

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation
