import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalGaussian
import OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses

/-! # Nonarchimedean Norm Gaussian -/

namespace OAI.RepresentationTheory.Theta.Adelic.NonarchimedeanNormGaussian

noncomputable section

/-! The Gaussian norm-character formula at every nonarchimedean place,
including the split quadratic algebra. -/

open OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [LocallyCompactSpace k]
variable [IsUltrametricDist k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
variable (d : k) (hd : d ≠ 0) (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
variable (hn : ∃ x : k, ψ x ≠ 1)

include hd hnd hc hu hn

omit [CompleteSpace k] in
theorem split_gaussian_pair (hsq : IsSquare d) (c : k) (hcz : c ≠ 0) :
    Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ c * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-d * c) = 1 := by
  obtain ⟨r, hr⟩ := hsq
  have hr2 : r ^ 2 = d := by simpa only [pow_two] using hr.symm
  have hr0 : r ≠ 0 := by intro hz; apply hd; simpa [hz] using hr2.symm
  let u : kˣ := Units.mk0 r hr0
  have hs := Weil.Local.GaussianSquareClasses.Construction.nonarchimedean_gaussianIndex_square_mul hnd ψ hu hc hn (-c) (neg_ne_zero.mpr hcz) u
  have hcoeff : -d * c = (-c) * u.val ^ 2 := by change -d * c = (-c) * r ^ 2; rw [hr2]; ring
  rw [hcoeff, hs, Weil.Local.GaussianNonarchimedean.Construction.nonarchimedean_gaussianIndex_neg hnd ψ hu hc hn c hcz]
  exact mul_inv_cancel₀ (Weil.Local.FunctionsMetaplectic.Construction.phase_ne_zero
    (Weil.Local.GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn c hcz).2)

theorem norm_character_gaussian_identity (a : kˣ) :
    (QuadraticNormCharacter.normSign d a : ℂ) * (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 2 * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-2 * d)) =
      Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (2 * a.val) * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-2 * d * a.val) := by
  by_cases hsq : IsSquare d
  · have h2 := split_gaussian_pair d hd hnd ψ hc hu hn hsq 2 (by norm_num)
    have ha := split_gaussian_pair d hd hnd ψ hc hu hn hsq (2 * a.val)
      (mul_ne_zero (by norm_num) a.ne_zero)
    have he2 : -(d : k) * 2 = -2 * d := by ring
    have hea : -(d : k) * (2 * a.val) = -2 * d * a.val := by ring
    rw [he2] at h2
    rw [hea] at ha
    rw [QuadraticNormCharacter.normSign_split d hd hsq a, Circle.coe_one, one_mul, h2, ha]
  · exact QuadraticLocalGaussian.norm_character_gaussian_identity d hd hsq hnd ψ hc hu hn a

end

end OAI.RepresentationTheory.Theta.Adelic.NonarchimedeanNormGaussian
