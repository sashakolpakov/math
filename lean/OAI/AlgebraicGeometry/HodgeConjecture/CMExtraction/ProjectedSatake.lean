import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.DualOccurrence
import OAI.RepresentationTheory.Hecke.SphericalActionModelInverse

/-! # Projected Satake -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedSatake.Iwasawa

noncomputable section

/-! A nonzero projected radial family supplies a scalar quotient carrying
the same occurring character and the complete SphericalAction conclusion. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

theorem projected_full_satake
    (q : ℕ) [Fact q.Prime] (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ V)
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] V) (M : ℕ) (hM : 0 < M)
    (j : ParameterChoices.Qbar →+* ℂ) (Ω : ParameterChoices.Qbar)
    (hΩ : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ Ω)‖ = 1)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j Ω • Θ b)
    (hHecke : ∀ T b, Θ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ) (P : Module.End ℂ V)
    (hP : ∀ T, Commute P (ρ T))
    (hspace : LinearMap.range P ≤ QuotientRadial.jointCharacterSpace q ρ (fun T => χ T))
    (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (hne : P (Θ b) ≠ 0) :
    ∃ (ℓ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ) (ρ₁ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ ℂ),
      ℓ ≠ 0 ∧
      RepresentationTheory.Hecke.SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset ρ₁ ℓ M (j Ω) ∧
      (∀ h z, ρ₁ h z = χ h * z) ∧
      (∃ z : ℂ, z ∈ LinearMap.range ℓ ∧ z ≠ 0 ∧ ∀ h, ρ₁ h z = χ h • z) := by
  obtain ⟨a, ha, _, _, ℓ, hℓ, hδ, hχ⟩ := Radial.DualOccurrence.Iwasawa.projected_dual_radial_occurring_satake
    q hElementaryDivisors ρ Θ M hM j Ω hΩ hrelation hHecke χ P hP hspace b hne
  let ρ₁ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ ℂ := (Algebra.lsmul ℂ ℂ ℂ).comp χ
  have hpow : ∀ (k : ℕ) (f : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q),
      ℓ ((Radial.Cyclicity.dilationEquiv q ^ k) f) = (j (a : ParameterChoices.Qbar)) ^ k * ℓ f := by
    intro k
    induction k with
    | zero => intro f; simp
    | succ k ih =>
      intro f
      rw [pow_succ', LinearEquiv.mul_apply, hδ, ih, pow_succ', mul_assoc]
  have hroot : (j (a : ParameterChoices.Qbar)) ^ M = j Ω := by rw [← map_pow, ha]
  have hsat := RepresentationTheory.Hecke.SphericalActionModelInverse.projective_satake_parameters_of_radial_quotient q .inverseCoset ℂ
    ρ₁ ℓ M hM (j Ω) (hΩ 1) (fun h f => hχ h f) (fun f => by
      change ℓ ((Radial.Cyclicity.dilationEquiv q ^ M) f) = j Ω * ℓ f
      rw [hpow, hroot])
  have hb : ∃ f, ℓ f ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hℓ (LinearMap.ext hh)
  obtain ⟨f, hf⟩ := hb
  exact ⟨ℓ, ρ₁, hℓ, hsat, fun _ _ => rfl, ℓ f, ⟨f, rfl⟩, hf, fun _ => rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectedSatake.Iwasawa
