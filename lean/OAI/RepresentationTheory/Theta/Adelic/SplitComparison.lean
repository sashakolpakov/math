import OAI.RepresentationTheory.Theta.Adelic.LocalKernel
import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest
import OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationLevi
import OAI.GroupTheory.LinearGroups.SpecialLinearPerfect

/-! # Split Comparison -/

namespace OAI.RepresentationTheory.Theta.Adelic.SplitComparison

noncomputable section

/-! The split-place substitution comparison for actual oscillator lifts.
The scalar character is constructed from the checked local commutant theorem;
SL3Perfect then removes it. Only the equality of the symplectic projections (the
stable-polarization coordinate condition) is an input. -/

open OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest.Construction
open OAI.RepresentationTheory.Weil.AdelicSplitting.NormalizationLevi.Construction OAI.RepresentationTheory.Theta.Adelic.LocalKernel

theorem scalar_difference_character
    {G S : Type*} [Group G] [AddCommGroup S] [Module ℂ S]
    (s t : G →* (S ≃ₗ[ℂ] S)) (f₀ : S) (hf₀ : f₀ ≠ 0)
    (hscalar : ∀ g, ∃ z : Circle, ∀ f, s g f = (z : ℂ) • t g f) :
    ∃ χ : G →* Circle, ∀ g f, s g f = (χ g : ℂ) • t g f := by
  choose c hc using hscalar
  have ht (g : G) : t g f₀ ≠ 0 :=
    fun h => hf₀ ((t g).injective (h.trans (map_zero _).symm))
  have h1 : c 1 = 1 := by
    apply Circle.coe_injective
    apply smul_left_injective ℂ hf₀
    simpa using (hc 1 f₀).symm
  have hmul (g h : G) : c (g * h) = c g * c h := by
    apply Circle.coe_injective
    apply smul_left_injective ℂ (ht (g * h))
    change (c (g * h) : ℂ) • t (g * h) f₀ = ((c g * c h : Circle) : ℂ) • t (g * h) f₀
    rw [Circle.coe_mul, ← hc (g * h) f₀, map_mul, map_mul,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hc g, hc h, map_smul, smul_smul]
  exact ⟨{ toFun := c, map_one' := h1, map_mul' := hmul }, hc⟩

variable {k : Type} [NormedField k] [IsUltrametricDist k] [CharZero k]
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x))
    (hu : ∀ x : k, ‖ψ x‖ = 1) (hk : ¬ DiscreteTopology k)
    (hn : ∃ x : k, ψ x ≠ 1)

include hc hu hk hn in
omit [SecondCountableTopology k] in
theorem sl3_same_projection_same_operator {N : ℕ}
    (s t : Matrix.SpecialLinearGroup (Fin 3) k →* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ)
    (hp : ∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (s g) = Weil.AdelicSplitting.Oscillator.Construction.localProjection k N ψ (t g)) :
    ∀ g f, Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (s g) f = Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (t g) f := by
  obtain ⟨χ, hχ⟩ := scalar_difference_character
    ((Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ).comp s) ((Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ).comp t)
    (Weil.UnitarySplitting.LocalTest.Construction.ultraTestVector k hk N) (Weil.UnitarySplitting.LocalTest.Construction.ultraTestVector_ne_zero k hk N)
    (fun g => LocalKernel.same_projection_operators hk N ψ hc hu hn (s g) (t g) (hp g))
  have hz := GroupTheory.LinearGroups.SpecialLinearPerfect.SLConstruction.sl3_hom_to_abelian_eq_one k Circle χ
  intro g f
  simpa only [hz, MonoidHom.one_apply, Circle.coe_one, one_smul, MonoidHom.comp_apply] using hχ g f

include hc hu hk hn in
theorem sl3_substitution
    (s : Matrix.SpecialLinearGroup (Fin 3) k →* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k 3 ψ)
    (hp : ∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k 3 ψ (s g) = Weil.Local.Generators.Construction.leviSymplectic (Matrix.SpecialLinearGroup.toGL g)) :
    ∀ g (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k 3) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k 3),
      (Weil.AdelicSplitting.Oscillator.Construction.localOperator k 3 ψ (s g) f).val x = f.val ((g⁻¹).val.mulVec x) := by
  let t := (Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom 3 ψ).comp (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin 3) k →* Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k 3)
  have he := sl3_same_projection_same_operator ψ hc hu hk hn s t hp
  intro g f x
  rw [he g f]
  change ((Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (Matrix.SpecialLinearGroup.toGL g)).val.2 f).val x = _
  rw [Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply]
  have hd : Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k (Matrix.SpecialLinearGroup.toGL g) = 1 := by
    apply Units.ext
    exact g.property
  rw [hd, Weil.Local.FunctionsMetaplectic.Construction.localModulus_one]
  rw [← map_inv]
  simp only [Real.sqrt_one, inv_one, Complex.ofReal_one, one_mul]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.SplitComparison
