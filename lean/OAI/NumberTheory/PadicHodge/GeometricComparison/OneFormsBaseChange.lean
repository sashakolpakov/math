import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # One Forms Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OneFormsBaseChange.FormsBaseChange

noncomputable section

/-! Actual algebraic one-forms commute with an affine scalar pushout, via their canonical Kahler differential interpretation. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

def oneFormEquiv (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A] :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 1 ≃ₗ[A] KaehlerDifferential R A :=
  (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A 1).trans (exteriorPower.oneEquiv A (KaehlerDifferential R A))

theorem oneFormEquiv_symbol (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra ℚ A] (a : A) (v : Fin 1 → A) :
    oneFormEquiv R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = a • KaehlerDifferential.D R A (v 0) := by
  rw [oneFormEquiv, LinearEquiv.trans_apply, AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv_symbol, map_smul]
  exact congrArg (fun x => a • x)
    (exteriorPower.oneEquiv_ιMulti (fun i => KaehlerDifferential.D R A (v i)))

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
  [Algebra ℚ A] [Algebra ℚ B]

def oneFormTensorEquiv : B ⊗[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 1 ≃ₗ[B] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B 1 :=
  ((oneFormEquiv R A).baseChange A B _ _).trans
    ((KaehlerDifferential.tensorKaehlerEquiv R S A B).trans (oneFormEquiv S B).symm)

theorem oneFormTensorEquiv_symbol (b : B) (a : A) (v : Fin 1 → A) :
    oneFormTensorEquiv R S A B (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  apply (oneFormEquiv S B).injective
  change oneFormEquiv S B ((oneFormEquiv S B).symm
    (KaehlerDifferential.tensorKaehlerEquiv R S A B
      ((oneFormEquiv R A).baseChange A B _ _ (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)))) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [LinearEquiv.baseChange_tmul, oneFormEquiv_symbol, TensorProduct.tmul_smul,
    oneFormEquiv_symbol]
  exact (KaehlerDifferential.tensorKaehlerEquiv_tmul_D R S A B (a • b) (v 0)).trans
    (congrArg (fun c => c • KaehlerDifferential.D S B (algebraMap A B (v 0)))
      (by rw [Algebra.smul_def, mul_comm]))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OneFormsBaseChange.FormsBaseChange
