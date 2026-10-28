import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.EvaluationField

/-! # Parameter Points -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ParameterPoints.Lifts

noncomputable section

/-!
Actual individually evaluated parameter points, constructed from the
native finite-etale parameter scheme. The finite extension and the
splitting are outputs of the construction, not supplied hypotheses.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory

universe u

structure FiniteEvaluationField (K : Type u) [Field K] (X : Over (Spec (.of K))) where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finite : Module.Finite K carrier]
  count : ℕ
  parameterIso : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of carrier)) (ULift.{u} (Fin count)) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K carrier)))).obj X

attribute [instance] FiniteEvaluationField.field FiniteEvaluationField.algebra FiniteEvaluationField.finite

def finiteEvaluationField (K : Type u) [Field K]
    (X : Over (Spec (.of K))) [IsFinite X.hom] [Etale X.hom] : FiniteEvaluationField K X :=
  Classical.choice (show Nonempty (FiniteEvaluationField K X) from by
    obtain ⟨L, _, _, _, n, ⟨e⟩⟩ := Intrinsic.EvaluationField.Lifts.native_finite_evaluation_field K X
    exact ⟨{ carrier := L, count := n, parameterIso := e }⟩)

namespace FiniteEvaluationField

variable {K : Type u} [Field K] {X : Over (Spec (.of K))}
variable (d : FiniteEvaluationField K X)

def labelPoint (i : ULift.{u} (Fin d.count)) :
    (𝟙_ (Over (Spec (.of d.carrier)))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))).obj X := by
  let a : Over.mk (𝟙 (Spec (.of d.carrier))) ⟶
      AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of d.carrier)) (ULift.{u} (Fin d.count)) :=
    Over.homMk (Sigma.ι (fun _ : ULift.{u} (Fin d.count) => Spec (.of d.carrier)) i)
      (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom i)
  exact a ≫ d.parameterIso.hom

/-- The evaluated point lies in the original parameter scheme, so its
image under the original target map defines a generic neighbor target. -/
def parameterPoint (i : ULift.{u} (Fin d.count)) : Spec (.of d.carrier) ⟶ X.left :=
  (d.labelPoint i).left ≫
    pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))

theorem parameterPoint_overBase (i : ULift.{u} (Fin d.count)) :
    d.parameterPoint i ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)) := by
  rw [FiniteEvaluationField.parameterPoint, Category.assoc, pullback.condition, ← Category.assoc]
  have h : (d.labelPoint i).left ≫
      pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier))) =
        𝟙 (Spec (.of d.carrier)) := (d.labelPoint i).w
  rw [h, Category.id_comp]

/-- Evaluate the independently specified target map at every parameter,
retaining the multiplicity of repeated target points. -/
def evaluatedTargets {Y : Scheme.{u}} (t : X.left ⟶ Y) :
    Multiset (Spec (.of d.carrier) ⟶ Y) :=
  Finset.univ.val.map (fun i => d.parameterPoint i ≫ t)

end FiniteEvaluationField

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ParameterPoints.Lifts
