import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftConstruction
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ChoiceEnumeration
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel

/-! # Reduction Specification -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification

noncomputable section

/-! Native output types for the NeighborCounting statement. The characteristic-zero
neighbors are indexed by the actual represented IsogenyQuotient parameter points.
Their complete kernels use the source polarization's canonical pairing.
Each target is a full PEL quotient, reduced by proper extension. No
multiplicity or special-kernel comparison occurs in these definitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.LiftConstruction.Lifts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family

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

abbrev genericSource : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N (Spec (.of L)) :=
  (ActionFamilyComparison.Family.actionFamily l.actionData).pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))

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

abbrev genericCanonicalPairing (i : Fin 3) :=
  AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j iota hsplit (l.genericPolarized (L := L)).abelian
    (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) s labels
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing (l.genericPolarized (L := L)).abelian
      (l.genericPolarized (L := L)).dual (l.genericPolarized (L := L)).polarization
      (q ^ HeckeExponents.neighborLevel i) (pow_pos (Fact.out : q.Prime).pos _))

variable (d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
  (HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
    (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels) h_TorsionQuotient))

abbrev evaluatedBase : Over (Spec (.of L)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)))

abbrev evaluatedChoice (i : Fin 3) (a : ULift (Fin (d.count (some i)))) :=
  AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates s (fun v => AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor (l.genericPolarized (L := L)).abelian.scheme
    (q ^ HeckeExponents.neighborLevel i) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents active multiplicative i v))
    (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) labels i v)) (.op (evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d))
    ((d.family (some i)).evaluatedChoiceEquiv
      (HeckeEvaluation.neighborChoiceFunctor (l.genericPolarized (L := L)).abelian q active multiplicative
        (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
          (l.genericAction (L := L)) labels) i)
      (HeckeEvaluation.nativeNeighborParameter (l.genericPolarized (L := L)).abelian q active multiplicative
        (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
          (l.genericAction (L := L)) labels) h_TorsionQuotient i).represents a)

abbrev evaluatedCompleteKernel (i : Fin 3) (a : ULift (Fin (d.count (some i)))) :=
  AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (q ^ HeckeExponents.neighborLevel i) s
    (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents active multiplicative i v))
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) s labels)
    (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
      (l.genericAction (L := L)) (HeckeExponents.neighborLevel i) s labels)
    (genericCanonicalPairing (L := L) j hsplit labels l i)
    (evaluatedChoice j hsplit labels active multiplicative h_TorsionQuotient l d i a)

variable [Algebra R d.carrier] [IsScalarTower R L d.carrier]
variable (v : EvaluationDVRLifts.EvaluationDVR R d.carrier)

/-- Output of the genuine generic quotient construction, for one actual
parameter. The target includes positive polarization, the normalized
Poincare bundle, the integral action, and every ordered level marking. -/
structure EvaluatedNativeNeighbor (i : Fin 3) (a : ULift (Fin (d.count (some i)))) where
  target : Evaluated.Targets.Lifts.EvaluatedTarget D v.carrier d.carrier ((algebraMap R v.carrier).comp b)
  model : (evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a).Model
  quotient : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny
    ((genericSource (L := L) l).pullback (evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom)
    (ActionFamilyComparison.Family.actionFamily (D.integral.universal.data.pullback target.map)) (q ^ HeckeExponents.neighborLevel i)
  kernel : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel quotient.isogeny.hom
    (AbelianScheme.IsogenyQuotient.Intrinsic.Stability.Construction.nativeSubgroupInclusion (l.genericPolarized (L := L)).abelian
      (evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d)
      (evaluatedCompleteKernel j hsplit labels active multiplicative h_TorsionQuotient l d i a) model)

/-- Reduce every original evaluated parameter once. Different generic
parameters can have the same special point and remain separate entries. -/
def nativeReducedNeighbors (hbase : Lifts.ResidueCompatible D R b residueIso)
    (Q : ∀ (i : Fin 3) (a : ULift (Fin (d.count (some i)))),
      EvaluatedNativeNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d v i a)
    (i : Fin 3) : Multiset D.GeometricPoint :=
  Finset.univ.val.map (fun a => (Q i a).target.specialPoint (ConstructedEvaluation.Lifts.evaluation_residueCompatible v hbase))

/-- The complete evaluated output for one source lift. The field splits
all original parameters and source torsion; the DVR and every genuine
quotient are existential outputs. The only multisets are reductions of
those quotient families and the stated ordinary operators. -/
def NativeReductionResult (hbase : Lifts.ResidueCompatible D R b residueIso)
    (X0 : D.OrdinaryPoint → D.OrdinaryPoint)
    (Y0 : D.OrdinaryPoint → Multiset D.OrdinaryPoint)
    (Z0 : D.OrdinaryPoint → D.OrdinaryPoint)
    (x : D.OrdinaryPoint) (l : Lifts.IntegralLift D R b residueIso x.val) : Prop :=
  ∃ d : Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField L
    (HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := L)).abelian q active multiplicative
      (CMPointsHeckeEvaluation.l45NeighborProjectors j iota hsplit (l.genericPolarized (L := L)).abelian
        (l.genericAction (L := L)) labels) h_TorsionQuotient),
  letI := d.scalarAlgebra R
  letI := d.scalarTower R
  ∃ v : EvaluationDVRLifts.EvaluationDVR R d.carrier,
    Nonempty (Lifts.IntegralLift D v.carrier ((algebraMap R v.carrier).comp b)
      (residueIso.trans v.residueIso) x.val) ∧
    ∃ Q : ∀ (i : Fin 3) (a : ULift (Fin (d.count (some i)))),
      EvaluatedNativeNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d v i a,
    let red := nativeReducedNeighbors j hsplit labels active multiplicative h_TorsionQuotient l d v hbase Q
    red 0 = {(X0 x).val} + q • ((Y0 x).map Subtype.val) ∧
    red 1 = ((Y0 (X0 x)).map Subtype.val) + q ^ 2 • {(Z0 x).val} ∧
    red 2 = {(Z0 (X0 x)).val}

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
