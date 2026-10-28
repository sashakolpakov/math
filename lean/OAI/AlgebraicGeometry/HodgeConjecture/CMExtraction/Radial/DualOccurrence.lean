import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DualRadial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.SatakeOccurrence

/-! # Dual Occurrence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.DualOccurrence.Iwasawa

noncomputable section

section

/-! Every image character for the inverse-transpose radial action has the
inverse-root kernel-torus evaluation, with the same algebraic dilation
root and a nonzero eigenfunctional. Raw GL3 minuscule normalization is
identified separately in NativeDualRadialRestriction. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]
  (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  (ρ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] Module.End ℂ W)

theorem dual_radial_generalized_occurring_character
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M) (ω : ℂ) (hω : ω ≠ 0)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b)
    (hHecke : ∀ T b, Θ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (w : W) (hw : w ∈ LinearMap.range Θ) (hne : w ≠ 0)
    (hχ : w ∈ QuotientRadial.jointCharacterSpace q ρ (fun T => χ T)) :
    ∃ (e : ℂ) (he : e ≠ 0), e ^ M = ω ∧ χ = DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.mk0 e he) := by
  let A := ContragredientRadial.Local.contragredientComplexHecke q
  let ρ' := ρ.comp A.toAlgHom
  let χ' := χ.comp A.toAlgHom
  have hHecke' : ∀ T b, Θ (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) = ρ' T (Θ b) := by
    intro T b
    have h := hHecke (A T) b
    change Θ (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors (A (A T)) b) = ρ' T (Θ b) at h
    rw [ContragredientRadial.Local.contragredientComplexHecke_involutive q T] at h
    exact h
  have hχ' : w ∈ QuotientRadial.jointCharacterSpace q ρ' (fun T => χ' T) := by
    simp only [QuotientRadial.jointCharacterSpace, Submodule.mem_iInf] at hχ ⊢
    exact fun T => hχ (A T)
  obtain ⟨e, he, hroot, hchar⟩ := QuotientRadial.radial_generalized_occurring_character q hElementaryDivisors ρ' Θ M hM ω hω
    hrelation hHecke' χ' w hw hne hχ'
  refine ⟨e, he, hroot, ?_⟩
  apply AlgHom.ext
  intro T
  have h := DFunLike.congr_fun hchar (A T)
  change χ (A (A T)) = Characters.radialCharacter q hElementaryDivisors e he (A T) at h
  rw [ContragredientRadial.Local.contragredientComplexHecke_involutive q T] at h
  exact h.trans (DFunLike.congr_fun (DualRadial.Iwasawa.radialCharacter_contragredient_eq_satake q hElementaryDivisors e he) T)

theorem dual_radial_generalized_occurring_satake
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M)
    (j : ParameterChoices.Qbar →+* ℂ) (ω : ParameterChoices.Qbar)
    (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j ω • Θ b)
    (hHecke : ∀ T b, Θ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (w : W) (hw : w ∈ LinearMap.range Θ) (hne : w ≠ 0)
    (hχ : w ∈ QuotientRadial.jointCharacterSpace q ρ (fun T => χ T)) :
    ∃ e : ParameterChoices.Qbarˣ, (e : ParameterChoices.Qbar) ^ M = ω ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ (e : ParameterChoices.Qbar))‖ = 1) ∧
      χ = DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.map j.toMonoidHom e) ∧
      ∃ ℓ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
        (∀ b, ℓ (Cyclicity.dilationEquiv q b) = j (e : ParameterChoices.Qbar) * ℓ b) ∧
        (∀ T b, ℓ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) = χ T * ℓ b) := by
  have hω0 : j ω ≠ 0 := by
    have h1 : ‖j ω‖ = 1 := by simpa using hω 1
    intro hzero
    simp [hzero] at h1
  obtain ⟨ec, hec, hroot, hchar⟩ := dual_radial_generalized_occurring_character q hElementaryDivisors ρ Θ M hM (j ω) hω0
    hrelation hHecke χ w hw hne hχ
  obtain ⟨e0, _, hj0, _, hroot0, _, _⟩ := Parameters.ParameterChoices.lift_dilation_root j ω M hM hω ec ec hroot (Or.inl rfl)
  have he0 : e0 ≠ 0 := by intro hz; exact hec (by rw [← hj0, hz, map_zero])
  let e : ParameterChoices.Qbarˣ := Units.mk0 e0 he0
  have heq : Units.map j.toMonoidHom e = Units.mk0 ec hec := Units.ext hj0
  refine ⟨e, hroot0, Parameters.ParameterChoices.root_all_conjugates_norm_one j ω e0 M hM hroot0 hω, ?_, ?_⟩
  · rw [heq, hchar]
  · refine ⟨Characters.dilationFunctional q ec, Characters.dilationFunctional_ne_zero q ec, ?_, ?_⟩
    · intro b
      rw [Characters.dilationFunctional_dilation q ec hec, show j (e : ParameterChoices.Qbar) = ec from hj0]
    · intro T b
      change Characters.dilationFunctional q ec
        (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors (ContragredientRadial.Local.contragredientComplexHecke q T) b) = _
      rw [Characters.dilationFunctional_hecke q hElementaryDivisors ec hec]
      have ht := DFunLike.congr_fun (DualRadial.Iwasawa.radialCharacter_contragredient_eq_satake q hElementaryDivisors ec hec) T
      change Characters.radialEigenvalue q hElementaryDivisors ec (ContragredientRadial.Local.contragredientComplexHecke q T) =
        DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.mk0 ec hec) T at ht
      rw [ht, hchar]

theorem dual_radial_occurring_character
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M) (ω : ℂ) (hω : ω ≠ 0)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = ω • Θ b)
    (hHecke : ∀ T b, Θ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (w : W) (hw : w ∈ LinearMap.range Θ) (hne : w ≠ 0)
    (hχ : ∀ T, ρ T w = χ T • w) :
    ∃ (e : ℂ) (he : e ≠ 0), e ^ M = ω ∧ χ = DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.mk0 e he) :=
  dual_radial_generalized_occurring_character q hElementaryDivisors ρ Θ M hM ω hω
    hrelation hHecke χ w hw hne (QuotientRadial.eigenvector_mem_jointCharacterSpace q ρ χ w hχ)

theorem dual_radial_occurring_satake
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M)
    (j : ParameterChoices.Qbar →+* ℂ) (ω : ParameterChoices.Qbar)
    (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j ω • Θ b)
    (hHecke : ∀ T b, Θ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (w : W) (hw : w ∈ LinearMap.range Θ) (hne : w ≠ 0)
    (hχ : ∀ T, ρ T w = χ T • w) :
    ∃ e : ParameterChoices.Qbarˣ, (e : ParameterChoices.Qbar) ^ M = ω ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ (e : ParameterChoices.Qbar))‖ = 1) ∧
      χ = DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.map j.toMonoidHom e) ∧
      ∃ ℓ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
        (∀ b, ℓ (Cyclicity.dilationEquiv q b) = j (e : ParameterChoices.Qbar) * ℓ b) ∧
        (∀ T b, ℓ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) = χ T * ℓ b) :=
  dual_radial_generalized_occurring_satake q hElementaryDivisors ρ Θ M hM j ω hω
    hrelation hHecke χ w hw hne (QuotientRadial.eigenvector_mem_jointCharacterSpace q ρ χ w hχ)

end

/-! A nonzero spectral projection of a radial theta class determines the
same algebraic dilation root. Commutation lets the entire radial family
pass through the projector, and generalized eigenspaces suffice. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]
  (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  (ρ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] Module.End ℂ W)

theorem projected_radial_occurring_satake
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M)
    (j : ParameterChoices.Qbar →+* ℂ) (ω : ParameterChoices.Qbar)
    (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j ω • Θ b)
    (hHecke : ∀ T b, Θ (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (P : Module.End ℂ W) (hP : ∀ T, Commute P (ρ T))
    (hspace : LinearMap.range P ≤ QuotientRadial.jointCharacterSpace q ρ (fun T => χ T))
    (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (hne : P (Θ b) ≠ 0) :
    ∃ e : ParameterChoices.Qbarˣ, (e : ParameterChoices.Qbar) ^ M = ω ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ (e : ParameterChoices.Qbar))‖ = 1) ∧
      χ = RadialSatake.Iwasawa.radialSatakeCharacter q (Units.map j.toMonoidHom e) ∧
      ∃ ℓ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
        (∀ a, ℓ (Cyclicity.dilationEquiv q a) = j (e : ParameterChoices.Qbar) * ℓ a) ∧
        (∀ T a, ℓ (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T a) = χ T * ℓ a) := by
  apply SatakeOccurrence.Iwasawa.radial_generalized_occurring_satake q hElementaryDivisors ρ (P.comp Θ) M hM j ω hω
    ?_ ?_ χ (P (Θ b)) ⟨b, rfl⟩ hne (hspace (LinearMap.mem_range_self P (Θ b)))
  · intro a
    change P (Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) a)) = j ω • P (Θ a)
    rw [hrelation, map_smul]
  · intro T a
    change P (Θ (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T a)) = ρ T (P (Θ a))
    rw [hHecke]
    exact LinearMap.congr_fun (hP T).eq (Θ a)

theorem projected_dual_radial_occurring_satake
    (Θ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] W) (M : ℕ) (hM : 0 < M)
    (j : ParameterChoices.Qbar →+* ℂ) (ω : ParameterChoices.Qbar)
    (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (hrelation : ∀ b, Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b) = j ω • Θ b)
    (hHecke : ∀ T b, Θ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T b) = ρ T (Θ b))
    (χ : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ)
    (P : Module.End ℂ W) (hP : ∀ T, Commute P (ρ T))
    (hspace : LinearMap.range P ≤ QuotientRadial.jointCharacterSpace q ρ (fun T => χ T))
    (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (hne : P (Θ b) ≠ 0) :
    ∃ e : ParameterChoices.Qbarˣ, (e : ParameterChoices.Qbar) ^ M = ω ∧
      (∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ (e : ParameterChoices.Qbar))‖ = 1) ∧
      χ = DualRadial.Iwasawa.dualRadialSatakeCharacter q (Units.map j.toMonoidHom e) ∧
      ∃ ℓ : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧
        (∀ a, ℓ (Cyclicity.dilationEquiv q a) = j (e : ParameterChoices.Qbar) * ℓ a) ∧
        (∀ T a, ℓ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T a) = χ T * ℓ a) := by
  apply dual_radial_generalized_occurring_satake q hElementaryDivisors ρ (P.comp Θ) M hM j ω hω
    ?_ ?_ χ (P (Θ b)) ⟨b, rfl⟩ hne (hspace (LinearMap.mem_range_self P (Θ b)))
  · intro a
    change P (Θ ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) a)) = j ω • P (Θ a)
    rw [hrelation, map_smul]
  · intro T a
    change P (Θ (ContragredientRadial.Local.contragredientRadialComplexAlgebra q hElementaryDivisors T a)) = ρ T (P (Θ a))
    rw [hHecke]
    exact LinearMap.congr_fun (hP T).eq (Θ a)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.DualOccurrence.Iwasawa
