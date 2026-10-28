import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison
import OAI.RepresentationTheory.Weil.Local.RealFourierLp

/-! # Fourier -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.Fourier.CM

noncomputable section

/-! The actual real Fourier automorphism in PoissonAutomorphy's coordinate and
negative-kernel convention, without a Weil-data input. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.SchwartzComparison.CM

def fourierEquiv (n : ℕ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n) :=
  (SchwartzComparison.CM.tests n).trans ((RepresentationTheory.Weil.Local.RealFourierLp.Construction.realBruhatFourier n).trans (SchwartzComparison.CM.tests n).symm)

theorem fourierEquiv_apply (n : ℕ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (x : Fin n → ℝ) :
    (fourierEquiv n f).val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f.val x := by
  change (RepresentationTheory.Weil.Local.RealFourierLp.Construction.realBruhatFourier n (SchwartzComparison.CM.tests n f)).val x = _
  rw [RepresentationTheory.Weil.Local.RealFourierLp.Construction.realBruhatFourier_apply, SchwartzComparison.CM.standard_character]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.Fourier.CM
