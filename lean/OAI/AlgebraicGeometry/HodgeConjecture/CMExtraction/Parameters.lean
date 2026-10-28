import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters
import OAI.RepresentationTheory.Hecke.RadialDilation.Cm

/-! # Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices

noncomputable section

/-! Lift the actual complex dilation parameters through the already chosen
complex embedding of Qbar. Polynomial identities and all-conjugate norms
are preserved, without choosing a second algebraic closure embedding. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM
open scoped Classical

def liftComplexAlgebraic (j : ParameterChoices.Qbar →+* ℂ) (z : ℂ) (hz : IsAlgebraic ℚ z) : ParameterChoices.Qbar :=
  (HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm ⟨z, hz.isIntegral⟩

theorem liftComplexAlgebraic_image (j : ParameterChoices.Qbar →+* ℂ) (z : ℂ) (hz : IsAlgebraic ℚ z) :
    j (liftComplexAlgebraic j z hz) = z := HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv_inverse j _

theorem finitePhase_isAlgebraic {z : ℂ} (hz : RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase z) :
    IsAlgebraic ℚ z := by
  obtain ⟨n, hn, he⟩ := hz
  apply IsAlgebraic.of_pow hn
  rw [he]
  exact isAlgebraic_one

theorem unitCircle_all_conjugates (j : ParameterChoices.Qbar →+* ℂ) (a : ParameterChoices.Qbar)
    (ha : RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle (j a)) :
    ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ a)‖ = 1 := by
  intro σ
  apply ha.2
  have he : minpoly ℚ (j a) = minpoly ℚ (σ a) :=
    (minpoly.algHom_eq j.toRatAlgHom j.injective a).trans (minpoly.algEquiv_eq σ a).symm
  rw [he]
  exact (Polynomial.aeval_algHom_apply j.toRatAlgHom (σ a) (minpoly ℚ (σ a))).trans
    (by rw [minpoly.aeval, map_zero])

theorem lift_dilation_parameters
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (j : ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    (hι : ∀ x : E, j (ιE x) = (x : ℂ))
    (reps : Finset Gal(E/ℚ)) (r : Eˣ) (d : Gal(E/ℚ) → ℤ) (ε : ℤ)
    (ωc ζc : ℂ) (hζ : RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ζc)
    (hω : RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle ωc)
    (hrel : ωc ^ 2 = ζc * ∏ τ ∈ reps,
      (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (ε * 3 * d τ)) :
    ∃ ω ζ : ParameterChoices.Qbar, j ω = ωc ∧ j ζ = ζc ∧
      (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
      ω ^ 2 = ζ * ∏ τ ∈ reps, (ιE (τ (r : E))) ^ (ε * 3 * d τ) ∧
      ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1 := by
  let ω := liftComplexAlgebraic j ωc hω.1
  let ζ := liftComplexAlgebraic j ζc (finitePhase_isAlgebraic hζ)
  have hωj : j ω = ωc := liftComplexAlgebraic_image j ωc hω.1
  have hζj : j ζ = ζc := liftComplexAlgebraic_image j ζc _
  refine ⟨ω, ζ, hωj, hζj, ?_, ?_, unitCircle_all_conjugates j ω (hωj.symm ▸ hω)⟩
  · obtain ⟨n, hn, he⟩ := hζ
    refine ⟨n, hn, j.injective ?_⟩
    rw [map_pow, hζj, he, map_one]
  · apply j.injective
    rw [map_pow, hωj, map_mul, hζj]
    simp only [map_prod, map_zpow₀, hι]
    exact hrel

theorem root_all_conjugates_norm_one (j : ParameterChoices.Qbar →+* ℂ) (ω e₀ : ParameterChoices.Qbar)
    (M : ℕ) (hM : 0 < M) (hroot : e₀ ^ M = ω)
    (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1) :
    ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ e₀)‖ = 1 := by
  intro σ
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hM.ne').mp
  rw [← norm_pow, ← map_pow, ← map_pow, hroot, hω σ]

theorem lift_dilation_root
    (j : ParameterChoices.Qbar →+* ℂ) (ω : ParameterChoices.Qbar) (M : ℕ) (hM : 0 < M)
    (hω : ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1)
    (e₀c ec : ℂ) (hroot : e₀c ^ M = j ω) (he : ec = e₀c ∨ ec = e₀c⁻¹) :
    ∃ e₀ e : ParameterChoices.Qbar, j e₀ = e₀c ∧ j e = ec ∧ e₀ ^ M = ω ∧
      (e = e₀ ∨ e = e₀⁻¹) ∧ ∀ σ : Gal(ParameterChoices.Qbar/ℚ), ‖j (σ e)‖ = 1 := by
  let : Algebra.IsAlgebraic ℚ ParameterChoices.Qbar := AlgebraicClosure.isAlgebraic ℚ
  have hωalg : IsAlgebraic ℚ (j ω) :=
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) ω).algHom j.toRatAlgHom
  have h₀alg : IsAlgebraic ℚ e₀c := IsAlgebraic.of_pow hM (hroot.symm ▸ hωalg)
  let e₀ := liftComplexAlgebraic j e₀c h₀alg
  have h₀j : j e₀ = e₀c := liftComplexAlgebraic_image j e₀c h₀alg
  have h₀pow : e₀ ^ M = ω := j.injective (by rw [map_pow, h₀j, hroot])
  have h₀unit := root_all_conjugates_norm_one j ω e₀ M hM h₀pow hω
  rcases he with rfl | rfl
  · exact ⟨e₀, e₀, h₀j, h₀j, h₀pow, Or.inl rfl, h₀unit⟩
  · refine ⟨e₀, e₀⁻¹, h₀j, ?_, h₀pow, Or.inr rfl, ?_⟩
    · rw [map_inv₀, h₀j]
    · intro σ
      rw [map_inv₀, map_inv₀, norm_inv, h₀unit σ, inv_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices
