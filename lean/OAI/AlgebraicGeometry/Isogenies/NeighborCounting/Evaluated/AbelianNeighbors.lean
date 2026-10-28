import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelModels
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledAbelian
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockStability

/-! # Abelian Neighbors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.AbelianNeighbors

noncomputable section

/-! Construct the actual abelian quotient for every original evaluated
parameter, including its full kernel, coefficient action and marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockStability.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledAbelian.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelModels

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]
variable {D : AbelianScheme.FrobeniusKernel.Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {R L : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [CharZero L] [Algebra R L] [IsFractionRing R L]
variable {b : B.R →+* R} {residueIso : AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.residueClosure q ≃+* IsLocalRing.ResidueField R}
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (hsplit : j.HasSplitCoordinates iota)
variable (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ)) (active : Fin s) (multiplicative : Fin s → Bool)
variable (h_TorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput) {x : D.GeometricPoint} (l : Lifts.IntegralLift D R b residueIso x)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (i : Fin 3) (v : Fin s) :
    Module (ZMod (q ^ HeckeExponents.neighborLevel i))
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents active multiplicative i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i)
    (HeckeExponents.neighborExponents active multiplicative i v) (HeckeExponents.neighborExponents_bound active multiplicative i v)

local instance chosenProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels i v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (.inl v)))

local instance oppositeProjectorGroup (i : Fin 3) (v : Fin s) :
    IsMonHom (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) s labels v) :=
  (l.genericAction (L := L)).preservesGroup
    (j.projector iota hsplit (HeckeExponents.neighborLevel i) (labels (.inr v)))

variable (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
    (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels) h_TorsionQuotient))

variable (i : Fin 3) (a : ULift (Fin (d.count (some i))))

omit [IsFractionRing R L] in
theorem evaluatedCompleteKernel_killed :
    (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a).KilledBy
      (q ^ HeckeExponents.neighborLevel i) :=
  AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel_killed (q ^ HeckeExponents.neighborLevel i) s _ _ _ _ _

def evaluatedAbelianNeighbor :=
  ModeledAbelian.Lifts.constructModeledAbelianQuotient (l.genericPolarized (L := L)).abelian
    (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d)
    (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (KernelModels.evaluatedCompleteKernelModel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (q ^ HeckeExponents.neighborLevel i) (𝟙 (Spec (.of L))) (pow_pos (Fact.out : q.Prime).pos _)
    (evaluatedCompleteKernel_killed j hsplit labels active multiplicative h_TorsionQuotient l d i a) h_TorsionQuotient

omit [IsFractionRing R L] in
theorem evaluatedCompleteKernel_stable (c : NumberField.RingOfIntegers E) :
    AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
      ((l.genericAction (L := L)).map c) := by
  apply AbelianScheme.IsogenyQuotient.BlockStability.Construction.choiceFullKernel_stable (q ^ HeckeExponents.neighborLevel i) s _ _ _ _ _
    ((l.genericAction (L := L)).map c)
    (fun v => ((j.residueCharacter iota (labels v) (HeckeExponents.neighborLevel i) c).val : ℤ))
  intro v
  have h := AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45_native_projector_scalar j iota hsplit (l.genericPolarized (L := L)).abelian
    (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) (labels v) c
  cases v <;> exact h

def evaluatedAbelianNeighborAction :=
  (evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a).action
    (l.genericAction (L := L))
    (evaluatedCompleteKernel_stable j hsplit labels active multiplicative h_TorsionQuotient l d i a)

def evaluatedAbelianNeighborLevel (hcop : q.Coprime N) :=
  (evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a).level N
    (hcop.pow_left (HeckeExponents.neighborLevel i))
    (((l.genericPolarized (L := L)).pullback
      (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom).level)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.AbelianNeighbors
