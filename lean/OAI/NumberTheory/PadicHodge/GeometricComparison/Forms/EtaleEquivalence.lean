import OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD
import Mathlib.RingTheory.Etale.Kaehler

/-! # Etale Equivalence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.EtaleEquivalence.FormsBaseChange

noncomputable section

/-! Actual differential forms commute with a flat formally étale extension of the coordinate algebra. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra ℚ A] [Algebra ℚ B] [Invertible (2 : A)]
  [Module.Flat A B] [Algebra.FormallyEtale A B]

def formsEtaleEquiv (n : ℕ) : B ⊗[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[B] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n :=
  ((AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A n).baseChange A B _ _).trans
    ((ExteriorPowerBaseChange.ExteriorBaseChange.powerEquiv A B (KaehlerDifferential R A) n).trans
      ((ExteriorPowerCongr.ExteriorBaseChange.powerCongr n
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B)).trans
          (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R B n).symm))

theorem formsEtaleEquiv_symbol (n : ℕ) (b : B) (a : A) (v : Fin n → A) :
    formsEtaleEquiv R A B n (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  apply (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R B n).injective
  simp only [formsEtaleEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul, AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol,
    TensorProduct.tmul_smul]
  refine (congrArg (ExteriorPowerCongr.ExteriorBaseChange.powerCongr n
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B))
    (ExteriorPowerBaseChange.ExteriorBaseChange.powerEquiv_tmul_ιMulti A B (KaehlerDifferential R A) n
      (a • b) (fun i => KaehlerDifferential.D R A (v i)))).trans ?_
  rw [map_smul, ExteriorPowerCongr.ExteriorBaseChange.powerCongr_ιMulti]
  have h : (fun i => KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B
      (1 ⊗ₜ[A] KaehlerDifferential.D R A (v i))) =
      fun i => KaehlerDifferential.D R B (algebraMap A B (v i)) := by
    funext i
    exact (congrArg (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap R A B (v i))).symm.trans
        ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).apply_symm_apply _)
  rw [h, Algebra.smul_def, mul_comm]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.EtaleEquivalence.FormsBaseChange
