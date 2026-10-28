import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RadialSatake
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters

/-! # Satake Occurrence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.SatakeOccurrence.Iwasawa

noncomputable section

/-! Every actual theta-image character has the normalized radial triple,
with an algebraic dilation root through the same chosen complex embedding.
The root has norm one at every conjugate. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices

variable (q : ℕ) [Fact q.Prime]

theorem radialTorusPoint_permutation (e : ℂˣ) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i,
      (SatakeParameters.Iwasawa.radialTorusPoint q e i : ℂ) =
        (![ (Real.sqrt (q : ℝ) : ℂ), (Real.sqrt (q : ℝ) : ℂ)⁻¹, e.val] : Fin 3 → ℂ) (σ i) := by
  refine ⟨(Equiv.swap 0 2).trans (Equiv.swap 0 1), ?_⟩
  intro i
  fin_cases i <;> norm_num [SatakeParameters.Iwasawa.radialTorusPoint, SatakeParameters.Iwasawa.sqrtUnit,
    RepresentationTheory.Satake.GL3TorusIwasawa.Normalization.residueSqrtUnit, Equiv.swap_apply_def, Fin.ext_iff]

theorem radial_generalized_occurring_satake
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] Module.End ℂ W)
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M)
    (j : ParameterChoices.Qbar →+* ℂ) (ω : ParameterChoices.Qbar)
    (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j ω • Θ b)
    (hHecke : ∀ T b, Θ (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (w : W) (hw : w ∈ LinearMap.range Θ) (hne : w ≠ 0)
    (hχ : w ∈ QuotientRadial.jointCharacterSpace q ρ (fun T => χ T)) :
    ∃ e : ParameterChoices.Qbarˣ, (e : ParameterChoices.Qbar) ^ M = ω ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ (e : ParameterChoices.Qbar))‖ = 1) ∧
      χ = RadialSatake.Iwasawa.radialSatakeCharacter q (Units.map j.toMonoidHom e) ∧
      ∃ ℓ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
        (∀ b, ℓ (Cyclicity.dilationEquiv q b) = j (e : ParameterChoices.Qbar) * ℓ b) ∧
        (∀ T b, ℓ (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) = χ T * ℓ b) := by
  have hω0 : j ω ≠ 0 := by
    have h1 : ‖j ω‖ = 1 := by simpa using hω 1
    intro hzero
    simp [hzero] at h1
  obtain ⟨ec, hec, hroot, hchar⟩ :=
    QuotientRadial.radial_generalized_occurring_character q hElementaryDivisors ρ Θ M hM (j ω) hω0 hrelation hHecke χ w hw hne hχ
  obtain ⟨e0, e1, hj0, hj1, hroot0, _, _⟩ :=
    Parameters.ParameterChoices.lift_dilation_root j ω M hM hω ec ec hroot (Or.inl rfl)
  have he0 : e0 ≠ 0 := by intro hz; exact hec (by rw [← hj0, hz, map_zero])
  let e : ParameterChoices.Qbarˣ := Units.mk0 e0 he0
  have heq : Units.map j.toMonoidHom e = Units.mk0 ec hec := Units.ext hj0
  refine ⟨e, hroot0, Parameters.ParameterChoices.root_all_conjugates_norm_one j ω e0 M hM hroot0 hω, ?_, ?_⟩
  · rw [heq, hchar, RadialSatake.Iwasawa.radialCharacter_eq_satake]
  · refine ⟨Characters.dilationFunctional q ec, Characters.dilationFunctional_ne_zero q ec, ?_, ?_⟩
    · intro b
      rw [Characters.dilationFunctional_dilation q ec hec, show j (e : ParameterChoices.Qbar) = ec from hj0]
    · intro T b
      rw [hchar]
      exact Characters.dilationFunctional_hecke q hElementaryDivisors ec hec T b

theorem radial_occurring_satake
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] Module.End ℂ W)
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M)
    (j : ParameterChoices.Qbar →+* ℂ) (ω : ParameterChoices.Qbar)
    (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j ω • Θ b)
    (hHecke : ∀ T b, Θ (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (w : W) (hw : w ∈ LinearMap.range Θ) (hne : w ≠ 0)
    (hχ : ∀ T, ρ T w = χ T • w) :
    ∃ e : ParameterChoices.Qbarˣ, (e : ParameterChoices.Qbar) ^ M = ω ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ (e : ParameterChoices.Qbar))‖ = 1) ∧
      χ = RadialSatake.Iwasawa.radialSatakeCharacter q (Units.map j.toMonoidHom e) ∧
      ∃ ℓ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
        (∀ b, ℓ (Cyclicity.dilationEquiv q b) = j (e : ParameterChoices.Qbar) * ℓ b) ∧
        (∀ T b, ℓ (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) = χ T * ℓ b) :=
  radial_generalized_occurring_satake q hElementaryDivisors ρ Θ M hM j ω hω hrelation hHecke χ w hw hne
    (QuotientRadial.eigenvector_mem_jointCharacterSpace q ρ (fun T => χ T) w hχ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.SatakeOccurrence.Iwasawa
