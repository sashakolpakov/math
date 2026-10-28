import OAI.RepresentationTheory.Weil.Local.Analytic
import OAI.RepresentationTheory.Weil.Local.RealReflectionLift
import OAI.RepresentationTheory.Theta.Adelic.NormalizedNormGaussian

/-! # General Split Gaussian -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeneralSplitGaussian

noncomputable section

/-! The corrected norm-form Weil constant is one at every split local
place, derived from the actual Gaussian limits. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [MeasurableSpace k] [BorelSpace k]
variable (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous ψ) (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)

include hc hu hn hnd

theorem gaussianIndex_neg (a : k) (ha : a ≠ 0) :
    Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-a) = (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ a)⁻¹ := by
  have hlim := ((Weil.Local.Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn 0).2.2.1 a ha).1
  have hne := ((Weil.Local.Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn 0).2.2.1 a ha).2.1
  have hconj : Tendsto (Weil.Local.FunctionsMetaplectic.Construction.regularizedGaussian k ψ (-a)) (𝓝[>] (0 : ℝ))
      (𝓝 (conj (Weil.Local.FunctionsMetaplectic.Construction.gaussianIntegral k ψ a))) := by
    have h := Complex.continuous_conj.continuousAt.tendsto.comp hlim
    convert h using 1
    funext ε
    exact Weil.Local.GaussianNonarchimedean.Construction.regularizedGaussian_neg ψ hu a ε
  have hG : Weil.Local.FunctionsMetaplectic.Construction.gaussianIntegral k ψ (-a) = conj (Weil.Local.FunctionsMetaplectic.Construction.gaussianIntegral k ψ a) := hconj.limUnder_eq
  rw [Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex, hG, Weil.Local.GaussianNonarchimedean.Construction.phase_conj]
  exact (Complex.inv_eq_conj (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex_norm k ψ a hne)).symm

theorem gaussianIndex_square (a : k) (ha : a ≠ 0) (b : kˣ) :
    Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (a * b.val ^ 2) = Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ a := by
  let : SecondCountableTopology k := Weil.Local.FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  exact Weil.Local.SquareDeterminantLift.Construction.gaussianIndex_square_mul_of_limit ψ a b
    (((Weil.Local.Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn 0).2.2.1 a ha).1)

theorem split_gaussian_pair (d : k) (hd : d ≠ 0) (hsq : IsSquare d)
    (a : k) (ha : a ≠ 0) : Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ a * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-d * a) = 1 := by
  obtain ⟨r, hr⟩ := hsq
  have hr2 : r ^ 2 = d := by simpa only [pow_two] using hr.symm
  have hr0 : r ≠ 0 := by intro hz; apply hd; simpa [hz] using hr2.symm
  let u : kˣ := Units.mk0 r hr0
  have hcoeff : -d * a = (-a) * u.val ^ 2 := by change -d * a = (-a) * r ^ 2; rw [hr2]; ring
  rw [hcoeff, gaussianIndex_square hnd ψ hc hu hn (-a) (neg_ne_zero.mpr ha) u,
    gaussianIndex_neg hnd ψ hc hu hn a ha]
  exact mul_inv_cancel₀ (Weil.Local.FunctionsMetaplectic.Construction.phase_ne_zero
    (((Weil.Local.Analytic.Construction.localField_analytic_normalization hnd ψ hc hu hn 0).2.2.1 a ha).2.1))

theorem schrodingerWeilConstant_split (d : k) (hd : d ≠ 0) (hsq : IsSquare d) :
    Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant k ψ d = 1 := by
  have h := split_gaussian_pair hnd ψ hc hu hn d hd hsq (-1) (neg_ne_zero.mpr one_ne_zero)
  simpa only [neg_mul_neg, mul_one, Weil.AdelicSplitting.CorrectedGeneratorKernels.Construction.schrodingerQuadraticWeilConstant] using h

end

end OAI.RepresentationTheory.Theta.Adelic.GeneralSplitGaussian
