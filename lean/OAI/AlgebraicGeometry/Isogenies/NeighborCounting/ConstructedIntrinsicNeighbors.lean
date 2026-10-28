import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PositivePEL
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ClassifiedFieldTarget
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELKernelTargetTransport

/-! # Constructed Intrinsic Neighbors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedIntrinsicNeighbors.Intrinsic

noncomputable section

/-! Construct the exact evaluated native neighbors required by NeighborCounting.
The positive PEL quotient is classified over the original finite
extension; every original complete kernel is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.KernelModels OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.AbelianNeighbors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.CanonicalIsotropy OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldPEL OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledFieldIntegralPEL
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionFamilyComparison.Family OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.PositivePEL
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ClassifiedFieldTarget OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELKernelTargetTransport

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

variable [Algebra R d.carrier] [IsScalarTower R L d.carrier]
variable (v : EvaluationDVRLifts.EvaluationDVR R d.carrier) (hgood : D.IsGoodCompletelySplitReduction)

variable (i : Fin 3) (a : ULift (Fin (d.count (some i))))

def evaluatedNeighborArithmeticBase : Spec (.of d.carrier) ⟶ B.base :=
  (Intrinsic.ReductionSpecification.evaluatedBase j hsplit labels active multiplicative h_TorsionQuotient l d).hom ≫
    (Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ Lifts.dvrBase R b)

omit [IsFractionRing R L] in
theorem evaluatedNeighborArithmeticBase_eq :
    evaluatedNeighborArithmeticBase j hsplit labels active multiplicative h_TorsionQuotient l d =
      Spec.map (CommRingCat.ofHom (algebraMap v.carrier d.carrier)) ≫
        Lifts.dvrBase v.carrier ((algebraMap R v.carrier).comp b) := by
  change Spec.map (CommRingCat.ofHom (algebraMap L d.carrier)) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ Spec.map (CommRingCat.ofHom b)) =
      Spec.map (CommRingCat.ofHom (algebraMap v.carrier d.carrier)) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap R v.carrier).comp b))
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext c
  exact (IsScalarTower.algebraMap_apply R L d.carrier (b c)).symm.trans
    (IsScalarTower.algebraMap_apply R v.carrier d.carrier (b c))

def evaluatedNeighborTarget :=
  ClassifiedFieldTarget.classifiedFieldTarget D v.carrier d.carrier ((algebraMap R v.carrier).comp b) hgood
    (evaluatedNeighborArithmeticBase j hsplit labels active multiplicative h_TorsionQuotient l d)
    (evaluatedNeighborArithmeticBase_eq j hsplit labels active multiplicative h_TorsionQuotient l d v)
    (Evaluated.PositivePEL.evaluatedNeighborIntegralObject j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)

def evaluatedNeighborTargetDataIso :=
  ClassifiedFieldTarget.classifiedFieldTargetDataIso D v.carrier d.carrier ((algebraMap R v.carrier).comp b) hgood
    (evaluatedNeighborArithmeticBase j hsplit labels active multiplicative h_TorsionQuotient l d)
    (evaluatedNeighborArithmeticBase_eq j hsplit labels active multiplicative h_TorsionQuotient l d v)
    (Evaluated.PositivePEL.evaluatedNeighborIntegralObject j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)

def constructedEvaluatedNativeNeighbor :
    Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor j hsplit labels active multiplicative h_TorsionQuotient l d v i a where
  target := evaluatedNeighborTarget j hsplit labels active multiplicative h_TorsionQuotient l d hlabels v hgood i a
  model := Evaluated.KernelModels.evaluatedCompleteKernelModel j hsplit labels active multiplicative h_TorsionQuotient l d i a
  quotient := (Evaluated.PositivePEL.evaluatedNeighborPELIsogeny j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a).transport
    (AbelianScheme.TateComparison.PELModuli.PELFamilyIso.refl _) (ActionFamilyComparison.Family.actionIsoToFamilyIso
      (evaluatedNeighborTargetDataIso j hsplit labels active multiplicative h_TorsionQuotient l d hlabels v hgood i a).symm)
  kernel := PELKernelTargetTransport.prescribedKernel_target_transport
    (Evaluated.PositivePEL.evaluatedNeighborPELIsogeny j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)
    (ActionFamilyComparison.Family.actionIsoToFamilyIso
      (evaluatedNeighborTargetDataIso j hsplit labels active multiplicative h_TorsionQuotient l d hlabels v hgood i a).symm)
    _ (Evaluated.PositivePEL.evaluatedNeighborPELIsogeny_kernel j hsplit labels active multiplicative h_TorsionQuotient l d hlabels i a)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedIntrinsicNeighbors.Intrinsic
