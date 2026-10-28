import OAI.RepresentationTheory.Weil.Local.NonarchimedeanOscillatorCharacter
import OAI.RepresentationTheory.Weil.Local.QuarterTurnKernel

/-! # Nonarchimedean Bare Kernel -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanBareKernel.Construction

noncomputable section

/-! The bare oscillator kernel consists of signs at every nonarchimedean place. -/

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)

include hnd hu hc hn in
theorem nonarchimedean_metaplectic_kernel_sign {n : ℕ}
    (a : FunctionsMetaplectic.Construction.Metaplectic k n ψ) (ha : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, a.val.val.2 f = ε • f := by
  by_cases hns : ∃ t : k, t ^ 2 = -1
  · obtain ⟨r, hr⟩ := hns
    exact QuarterTurnKernel.Construction.nonarchimedean_metaplectic_kernel_sign_of_sqrt_neg_one hnd ψ hu hc hn r hr a ha
  · obtain ⟨Θ, hΘ⟩ := NonarchimedeanOscillatorCharacter.Construction.exists_nonarchimedean_oscillator_character hnd ψ hu hc hn hns n
    have hle : FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ ≤ Θ.ker := by
      change Subgroup.closure (commutatorSet (FunctionsMetaplectic.Construction.Oscillator k n ψ) ∪ {FunctionsMetaplectic.Construction.oscillatorMinus k n ψ}) ≤ Θ.ker
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · obtain ⟨b, c, rfl⟩ := hx
        change Θ (b * c * b⁻¹ * c⁻¹) = 1
        simp only [map_mul, map_inv]
        rw [mul_right_comm]
        group
      · obtain rfl := Set.mem_singleton_iff.mp hx
        change Θ (FunctionsMetaplectic.Construction.oscillatorMinus k n ψ) = 1
        rw [hΘ (FunctionsMetaplectic.Construction.oscillatorMinus k n ψ) (-1) rfl (fun f => by
          change -f = (-1 : ℂ) • f
          exact (neg_one_smul ℂ f).symm)]
        apply Units.ext
        norm_num
    obtain ⟨z, hz, hscalar⟩ := BruhatCosets.Construction.nonarchimedean_oscillator_kernel_unit_scalar hnd ψ hu hc hn a.val ha
    have hz0 : z ≠ 0 := by intro he; simp [he] at hz
    have he : Θ a.val = 1 := hle a.property
    rw [hΘ a.val (Units.mk0 z hz0) ha hscalar] at he
    exact ⟨z, congrArg Units.val he, hscalar⟩

include hnd hu hc hn in
theorem nonarchimedean_metaplectic_same_projection_sign {n : ℕ}
    (a b : FunctionsMetaplectic.Construction.Metaplectic k n ψ)
    (hab : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ a = FunctionsMetaplectic.Construction.metaplecticProjection k n ψ b) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
      FunctionsMetaplectic.Construction.weilRepresentation k n ψ a f = ε • FunctionsMetaplectic.Construction.weilRepresentation k n ψ b f := by
  have hker : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨ε, hε, h⟩ := nonarchimedean_metaplectic_kernel_sign hnd ψ hu hc hn (a * b⁻¹) hker
  refine ⟨ε, hε, fun f => ?_⟩
  have hh := h (b.val.val.2 f)
  change a.val.val.2 (b.val.val.2.symm (b.val.val.2 f)) = ε • b.val.val.2 f at hh
  simpa only [LinearEquiv.symm_apply_apply] using! hh

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanBareKernel.Construction
