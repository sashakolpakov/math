import OAI.RepresentationTheory.Weil.UnitarySplitting.Kernel
import OAI.RepresentationTheory.Theta.Adelic.SplitComparison
import OAI.RepresentationTheory.Theta.Adelic.TensorProjective

/-! # Arch Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.ArchComparison

noncomputable section

/-! Continuous comparison characters for the actual local oscillator
extension, including archimedean fields. The comparison is recovered from
L² matrix coefficients, not assumed as part of a splitting interface. -/

open scoped InnerProductSpace

open OAI.RepresentationTheory.Weil.UnitarySplitting.Kernel.Construction

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
    (hu : ∀ x : k, ‖ψ x‖ = 1) (hk : ¬ DiscreteTopology k)
    (hn : ∃ x : k, ψ x ≠ 1) {N : ℕ}

include hc hu hk hn in
theorem kernel_scalar (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (ha : Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a = 1) :
    ∃ z : Circle, Weil.AdelicSplitting.Oscillator.Construction.localScalar k N ψ z = a := by
  have hcomm (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
      a.val.2 (Weil.UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f) =
        Weil.UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v (a.val.2 f) := by
    have hgraph : Weil.Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ v f (Weil.UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f) := rfl
    have h := (a.property.2 v f (Weil.UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f)).mp hgraph
    change (a.val.2 (Weil.UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v f)).val =
      Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction a.val.1 v) (a.val.2 f).val at h
    change a.val.1 = 1 at ha
    rw [ha, Weil.Local.FunctionsMetaplectic.Construction.symplecticAction_one] at h
    exact Subtype.ext h
  obtain ⟨z, hz⟩ := Weil.UnitarySplitting.Kernel.Construction.unitary_heisenberg_commutant_scalar hk ψ hc hu hn
    a.val.2.toLinearMap a.property.1 hcomm
  refine ⟨z, ?_⟩
  apply Subtype.ext
  apply Prod.ext ha.symm
  apply LinearEquiv.ext
  intro f
  exact (hz f).symm

include hc hu hk hn in
theorem same_projection_scalar (a b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (hp : Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ a = Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ b) :
    ∃ z : Circle, ∀ f, Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f = (z : ℂ) • Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ b f := by
  have hh : Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hp, mul_inv_cancel]
  obtain ⟨z, hz⟩ := kernel_scalar ψ hc hu hk hn (a * b⁻¹) hh
  have heq : a = Weil.AdelicSplitting.Oscillator.Construction.localScalar k N ψ z * b := by rw [hz]; simp
  refine ⟨z, fun f => ?_⟩
  rw [heq, map_mul, LinearEquiv.mul_apply, Weil.AdelicSplitting.Oscillator.Construction.localOperator_scalar]

include hc hu hk hn in
theorem continuous_comparison_character
    {G : Type*} [Group G] [TopologicalSpace G]
    (s t : G →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (hp : ∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (s g) = Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (t g)) :
    ∃ χ : G →ₜ* Circle, ∀ g f,
      Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (s g) f = (χ g : ℂ) • Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (t g) f := by
  let : SecondCountableTopology k := Weil.UnitarySplitting.TestSpaceAnalysis.Construction.localField_secondCountable k hk
  obtain ⟨f₀, hf₀⟩ := Weil.UnitarySplitting.LocalTest.Construction.exists_test_nonzero k hk N
  obtain ⟨χ, hχ⟩ := SplitComparison.scalar_difference_character
    ((Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ).comp s.toMonoidHom) ((Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ).comp t.toMonoidHom)
    f₀ hf₀ (fun g => same_projection_scalar ψ hc hu hk hn (s g) (t g) (hp g))
  let a := fun g : G => Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (s g) f₀)
  let b := fun g : G => Weil.UnitarySplitting.Weak.Construction.testToL2 k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (t g) f₀)
  have ha : Continuous a :=
    (TensorProjective.Smoothness.local_orbit_L2_continuous k N ψ f₀).comp s.continuous
  have hb : Continuous b :=
    (TensorProjective.Smoothness.local_orbit_L2_continuous k N ψ f₀).comp t.continuous
  have hbn (g : G) : b g ≠ 0 := by
    intro h
    have hh : Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (t g) f₀ = 0 :=
      Weil.UnitarySplitting.Weak.Construction.testToL2_injective k N (h.trans (map_zero _).symm)
    exact hf₀ ((Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (t g)).injective (hh.trans (map_zero _).symm))
  have hden (g : G) : ⟪b g, b g⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr (hbn g)
  have hformula (g : G) : (χ g : ℂ) = ⟪b g, a g⟫_ℂ / ⟪b g, b g⟫_ℂ := by
    have hh : a g = (χ g : ℂ) • b g := by
      exact (congrArg (Weil.UnitarySplitting.Weak.Construction.testToL2 k N) (hχ g f₀)).trans (map_smul _ _ _)
    rw [hh, inner_smul_right, mul_div_cancel_right₀ _ (hden g)]
  have hcontinuous : Continuous (fun g : G => (χ g : ℂ)) := by
    simp_rw [hformula]
    exact (hb.inner ha).div (hb.inner hb) hden
  refine ⟨⟨χ, hcontinuous.subtype_mk _⟩, ?_⟩
  intro g f
  exact hχ g f

end

end OAI.RepresentationTheory.Theta.Adelic.ArchComparison
