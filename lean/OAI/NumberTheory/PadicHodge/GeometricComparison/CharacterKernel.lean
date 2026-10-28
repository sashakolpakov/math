import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CharacterRange

/-! # Character Kernel -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CharacterKernel.GeneralizedHecke

noncomputable section

/-! A character occurring in a nonzero generalized eigenspace annihilates the kernel of the original rational realization. -/

open scoped TensorProduct

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem eigenvalue_zero_of_zero_operator (μ : K) (x : V) (hx : x ≠ 0)
    (hmem : x ∈ (0 : Module.End K V).maxGenEigenspace μ) : μ = 0 := by
  have hne : (0 : Module.End K V).maxGenEigenspace μ ≠ ⊥ := by
    intro hbot
    exact hx (by simpa only [hbot, Submodule.mem_bot] using hmem)
  have hone : (0 : Module.End K V).HasUnifEigenvalue μ 1 :=
    (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (show (0 : ℕ∞) < ⊤ by simp)).mp hne
  obtain ⟨v, hv⟩ := hone.exists_hasUnifEigenvector
  have he := hv.apply_eq_smul
  change (0 : V) = μ • v at he
  exact (smul_eq_zero.mp he.symm).resolve_right hv.2

variable {H E L : Type*} [CommRing H] [Algebra K H]
  [Field E] [Algebra K E] [Field L] [Algebra K L]

theorem character_ker_le (ρ : H →ₐ[K] Module.End K V) (χ : H →ₐ[K] E) (ι : E →ₐ[K] L)
    (hS : Linear.generalizedHeckeSummand (fun h => (ρ h).baseChange L) (fun h => ι (χ h)) ≠ ⊥) :
    ρ.toLinearMap.ker ≤ χ.toLinearMap.ker := by
  obtain ⟨x, hx, hxzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  intro h hh
  have he : ρ h = 0 := hh
  have hm := (Linear.mem_generalizedHeckeSummand _ _ x).mp hx h
  rw [he, LinearMap.baseChange_zero] at hm
  change χ h = 0
  apply ι.injective
  rw [map_zero]
  exact eigenvalue_zero_of_zero_operator (ι (χ h)) x hxzero hm

theorem finite_character_range_of_summand [FiniteDimensional K V]
    (ρ : H →ₐ[K] Module.End K V) (χ : H →ₐ[K] E) (ι : E →ₐ[K] L)
    (hS : Linear.generalizedHeckeSummand (fun h => (ρ h).baseChange L) (fun h => ι (χ h)) ≠ ⊥) :
    FiniteDimensional K χ.toLinearMap.range :=
  Finite.CharacterRange.GeneralizedHecke.finite_range_of_ker_le ρ.toLinearMap χ.toLinearMap (character_ker_le ρ χ ι hS)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CharacterKernel.GeneralizedHecke
