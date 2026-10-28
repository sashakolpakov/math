import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.Enumeration
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers

/-! # Choice Enumeration -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated

noncomputable section

/-! The independently evaluated native parameter family can be indexed
by its actual represented subgroup choices. The equivalence is constructed
from evaluation and representability, with every repeated target retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction

variable {K : Type u} [Field K] {X : Over (Spec (.of K))}
variable (d : ParameterPoints.Lifts.FiniteEvaluationField K X)
variable (F : (Over (Spec (.of K)))ᵒᵖ ⥤ Type (u + 1)) (repr : F.RepresentableBy X)

def ParameterPoints.Lifts.FiniteEvaluationField.evaluatedChoiceEquiv : ULift.{u} (Fin d.count) ≃
    F.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier))))) :=
  d.parameterPointEquiv.trans repr.homEquiv

theorem ParameterPoints.Lifts.FiniteEvaluationField.evaluatedChoiceEquiv_point (i : ULift.{u} (Fin d.count)) :
    (repr.homEquiv.symm (d.evaluatedChoiceEquiv F repr i)).left = d.parameterPoint i := by
  change (repr.homEquiv.symm (repr.homEquiv (d.parameterPointEquiv i))).left = _
  rw [Equiv.symm_apply_apply]
  exact d.parameterPointEquiv_left i

/-- This equality uses the original target morphism on the original
parameter scheme; no reduced target or operator identity is a premise. -/
theorem ParameterPoints.Lifts.FiniteEvaluationField.evaluatedTargets_via_choices {Y : Scheme.{u}} (t : X.left ⟶ Y) :
    letI : Finite (F.obj (.op
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))))) :=
        Finite.of_equiv _ (d.evaluatedChoiceEquiv F repr)
    d.evaluatedTargets t = AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset (fun c : F.obj (.op
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier))))) =>
        (repr.homEquiv.symm c).left ≫ t) := by
  let : Finite (F.obj (.op
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))))) :=
        Finite.of_equiv _ (d.evaluatedChoiceEquiv F repr)
  have h := AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset_reindex (d.evaluatedChoiceEquiv F repr)
    (fun i => d.parameterPoint i ≫ t)
  have hstart : d.evaluatedTargets t = AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset (fun i => d.parameterPoint i ≫ t) := by
    unfold ParameterPoints.Lifts.FiniteEvaluationField.evaluatedTargets AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.finiteTargetMultiset
    exact congrArg (fun I : Fintype (ULift.{u} (Fin d.count)) =>
      (@Finset.univ _ I).val.map (fun i => d.parameterPoint i ≫ t)) (Subsingleton.elim _ _)
  refine hstart.trans (h.trans ?_)
  congr 1
  funext c
  change d.parameterPoint ((d.evaluatedChoiceEquiv F repr).symm c) ≫ t = _
  rw [← d.evaluatedChoiceEquiv_point F repr, Equiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated
