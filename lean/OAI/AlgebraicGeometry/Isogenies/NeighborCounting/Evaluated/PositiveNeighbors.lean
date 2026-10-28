import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.CanonicalIsotropy
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPolarization

/-! # Positive Neighbors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PositiveNeighbors

noncomputable section

/-! Positive polarization and normalized dual data for every literal
original evaluated neighbor, with the original complete quotient and
all ordered level markings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelModels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.AbelianNeighbors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.CanonicalIsotropy OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPolarization

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

variable (hlabels : ∀ v, labels (Sum.swap v) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels v)

variable (i : Fin 3) (a : ULift (Fin (d.count (some i))))

def evaluatedNeighborDual :=
  ModeledFieldPolarization.modeledFieldDual (l.genericPolarized (L := L))
    (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom
    (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (KernelModels.evaluatedCompleteKernelModel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _)
    (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a)

def evaluatedNeighborPolarization :=
  ModeledFieldPolarization.modeledFieldPolarization (l.genericPolarized (L := L))
    (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom
    (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (KernelModels.evaluatedCompleteKernelModel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _)
    (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (D.polarizationPrimeToQ.pow_left (HeckeExponents.neighborLevel i))
    (CanonicalIsotropy.evaluatedCompleteKernel_self_annihilating j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)

def evaluatedNeighborPolarized :=
  ModeledFieldPolarization.modeledFieldPolarized (l.genericPolarized (L := L))
    (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom
    (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (KernelModels.evaluatedCompleteKernelModel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _)
    (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (D.polarizationPrimeToQ.pow_left (HeckeExponents.neighborLevel i))
    (CanonicalIsotropy.evaluatedCompleteKernel_self_annihilating j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)
    (D.levelPrimeToQ.pow_left (HeckeExponents.neighborLevel i))

abbrev evaluatedNeighborPolarization_nativePullback :=
  ModeledFieldPolarization.modeledFieldPolarization_nativePullback (l.genericPolarized (L := L))
    (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom
    (Intrinsic.ReductionSpecification.evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (KernelModels.evaluatedCompleteKernelModel j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _)
    (AbelianNeighbors.evaluatedAbelianNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d i a)
    (D.polarizationPrimeToQ.pow_left (HeckeExponents.neighborLevel i))
    (CanonicalIsotropy.evaluatedCompleteKernel_self_annihilating j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PositiveNeighbors
