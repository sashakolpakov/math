import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELSourceIso
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.GenericAction

/-! # Intrinsic Integral Isogeny -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntrinsicIntegralIsogeny.Intrinsic

noncomputable section

/-! Put an actual evaluated native neighbor on the generic fibers of
its original integral source and its independent proper target model.
Both full PEL comparisons are constructed from the given scalar towers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PELSourceIso

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

variable [Algebra R d.carrier] [IsScalarTower R L d.carrier]
variable (v : EvaluationDVRLifts.EvaluationDVR R d.carrier)
  (i : Fin 3) (a : ULift (Fin (d.count (some i))))
  (Q : Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d v i a)

def evaluatedNativeIntegralIsogeny :
    AbelianScheme.TateComparison.PELIsogenies.PELIsogeny
      ((ActionFamilyComparison.Family.actionFamily (l.overEvaluationDVR v).actionData).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap v.carrier d.carrier))))
      ((ActionFamilyComparison.Family.actionFamily Q.target.actionData).pullback
        (Spec.map (CommRingCat.ofHom (algebraMap v.carrier d.carrier))))
      (q ^ HeckeExponents.neighborLevel i) :=
  Q.quotient.transport (PELSourceIso.evaluatedGenericSourceFamilyIso (F := L) l v).symm Q.target.genericFamilyIso.symm

omit [IsFractionRing R L] in
theorem evaluatedNativeIntegralIsogeny_hom :
    (evaluatedNativeIntegralIsogeny j hsplit labels active multiplicative h_TorsionQuotient l d v i a Q).isogeny.hom =
      (PELSourceIso.evaluatedGenericSourceFamilyIso (F := L) l v).abelian.inv ≫
        Q.quotient.isogeny.hom ≫ Q.target.genericFamilyIso.abelian.inv :=
  AbelianScheme.TateComparison.PELIsogenies.PELIsogeny.transport_hom Q.quotient
    (PELSourceIso.evaluatedGenericSourceFamilyIso (F := L) l v).symm Q.target.genericFamilyIso.symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.IntrinsicIntegralIsogeny.Intrinsic
