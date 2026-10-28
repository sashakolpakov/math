import OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr
import OAI.NumberTheory.PadicHodge.GeometricComparison.OneFormsBaseChange

/-! # Tensor Equivalence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.TensorEquivalence.FormsBaseChange

noncomputable section

/-! The actual differential-form presentation commutes with flat affine base change in every degree. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
  [Algebra ℚ A] [Algebra ℚ B] [Invertible (2 : A)] [Module.Flat A B]

def formsTensorEquiv (n : ℕ) : B ⊗[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[B] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B n :=
  ((AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A n).baseChange A B _ _).trans
    ((ExteriorPowerBaseChange.ExteriorBaseChange.powerEquiv A B (KaehlerDifferential R A) n).trans
      ((ExteriorPowerCongr.ExteriorBaseChange.powerCongr n (KaehlerDifferential.tensorKaehlerEquiv R S A B)).trans
        (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv S B n).symm))

theorem formsTensorEquiv_symbol (n : ℕ) (b : B) (a : A) (v : Fin n → A) :
    formsTensorEquiv R S A B n (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  apply (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv S B n).injective
  simp only [formsTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul, AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol,
    TensorProduct.tmul_smul]
  refine (congrArg (ExteriorPowerCongr.ExteriorBaseChange.powerCongr n
      (KaehlerDifferential.tensorKaehlerEquiv R S A B))
    (ExteriorPowerBaseChange.ExteriorBaseChange.powerEquiv_tmul_ιMulti A B (KaehlerDifferential R A) n
      (a • b) (fun i => KaehlerDifferential.D R A (v i)))).trans ?_
  rw [map_smul, ExteriorPowerCongr.ExteriorBaseChange.powerCongr_ιMulti]
  have h : (fun i => KaehlerDifferential.tensorKaehlerEquiv R S A B
      (1 ⊗ₜ[A] KaehlerDifferential.D R A (v i))) =
      fun i => KaehlerDifferential.D S B (algebraMap A B (v i)) := by
    funext i
    exact (KaehlerDifferential.tensorKaehlerEquiv_tmul_D R S A B 1 (v i)).trans
      (one_smul B _)
  rw [h, Algebra.smul_def, mul_comm]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.TensorEquivalence.FormsBaseChange
