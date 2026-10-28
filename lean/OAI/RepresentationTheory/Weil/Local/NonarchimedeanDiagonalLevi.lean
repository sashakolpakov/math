import OAI.RepresentationTheory.Weil.Local.NonarchimedeanDiagonalLift
import OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses

/-! # Nonarchimedean Diagonal Levi -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanDiagonalLevi.Construction

noncomputable section

/-! Bare diagonal Levi lifts obtained from two concretely normalized Weyl lifts. -/

open _root_.Matrix

theorem exists_nonarchimedean_inverse_diagonal_levi_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) (a : Fin n → kˣ) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic k n ψ,
      FunctionsMetaplectic.Construction.metaplecticProjection k n ψ m = Generators.Construction.leviSymplectic (DiagonalAlgebra.Construction.diagonalGeneralLinear a)⁻¹ ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
        FunctionsMetaplectic.Construction.weilRepresentation k n ψ m f =
          ((∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n) •
            (LinearIntertwiner.Construction.linearOscillator ψ (DiagonalAlgebra.Construction.diagonalGeneralLinear a)⁻¹).val.2 f := by
  obtain ⟨F, hFπ, hFop⟩ := NormalizedFresnel.Construction.exists_nonarchimedean_normalized_fourier_oscillator hNondiscrete n ψ hu hc hn
  obtain ⟨v, hv, hvo⟩ := NonarchimedeanDiagonalLift.Construction.exists_nonarchimedean_diagonal_weyl_metaplectic hNondiscrete ψ hu hc hn a F hFπ hFop
  obtain ⟨w, hw, hwo⟩ := NormalizedFresnel.Construction.exists_nonarchimedean_weyl_metaplectic hNondiscrete n ψ hu hc hn
  let D := DiagonalAlgebra.Construction.diagonalGeneralLinear a
  let Li := (LinearIntertwiner.Construction.linearOscillator ψ D⁻¹).val.2
  have hLL (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : Li ((LinearIntertwiner.Construction.linearOscillator ψ D).val.2 f) = f := by
    have h := LinearOscillatorHom.Construction.linearOscillator_mul ψ D⁻¹ D
    rw [inv_mul_cancel, LinearOscillatorHom.Construction.linearOscillator_one] at h
    exact congrArg (fun b : FunctionsMetaplectic.Construction.Oscillator k n ψ => b.val.2 f) h.symm
  have hΓ : (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact FunctionsMetaplectic.Construction.phase_ne_zero (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hn (a i).val (a i).ne_zero).2
  refine ⟨w * v⁻¹, ?_, fun f => ?_⟩
  · rw [map_mul, map_inv, hw, hv, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
    exact ((GenerationSymplectic.Construction.leviHom (k := k) (n := n)).map_inv D).symm
  · let g := FunctionsMetaplectic.Construction.weilRepresentation k n ψ v⁻¹ f
    have hvg : FunctionsMetaplectic.Construction.weilRepresentation k n ψ v g = f := LinearEquiv.apply_symm_apply _ _
    have he := congrArg Li (hvo g)
    rw [hvg, map_smul, hLL] at he
    have hFg : F.val.2 g = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) • Li f := by
      have h := congrArg (fun z : FunctionsMetaplectic.Construction.schwartzBruhat k n => (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) • z) he
      simpa only [smul_smul, mul_inv_cancel₀ hΓ, one_smul] using h.symm
    apply Subtype.ext
    funext x
    change (FunctionsMetaplectic.Construction.weilRepresentation k n ψ w g).val x =
      ((∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n) * (Li f).val x
    rw [hwo, ← hFop, hFg]
    change (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n)⁻¹ * ((∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) * (Li f).val x) = _
    ring

theorem nonarchimedean_gaussianIndex_inverse
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) (a : kˣ) :
    FunctionsMetaplectic.Construction.gaussianIndex k ψ ((a⁻¹).val) = FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val := by
  have h := GaussianSquareClasses.Construction.nonarchimedean_gaussianIndex_square_mul hNondiscrete ψ hu hc hn
    (a⁻¹).val (a⁻¹).ne_zero a
  have he : (a⁻¹).val * a.val ^ 2 = a.val := by
    rw [Units.val_inv_eq_inv_val]
    field_simp
  rw [he] at h
  exact h.symm

theorem exists_nonarchimedean_diagonal_levi_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) (a : Fin n → kˣ) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic k n ψ,
      FunctionsMetaplectic.Construction.metaplecticProjection k n ψ m = Generators.Construction.leviSymplectic (DiagonalAlgebra.Construction.diagonalGeneralLinear a) ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
        FunctionsMetaplectic.Construction.weilRepresentation k n ψ m f =
          ((∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n) •
            (LinearIntertwiner.Construction.linearOscillator ψ (DiagonalAlgebra.Construction.diagonalGeneralLinear a)).val.2 f := by
  obtain ⟨m, hm, hma⟩ := exists_nonarchimedean_inverse_diagonal_levi_metaplectic hNondiscrete ψ hu hc hn
    (fun i => (a i)⁻¹)
  have hD : (DiagonalAlgebra.Construction.diagonalGeneralLinear (fun i => (a i)⁻¹))⁻¹ = DiagonalAlgebra.Construction.diagonalGeneralLinear a := by
    rw [← DiagonalAlgebra.Construction.diagonalGeneralLinear_inv, inv_inv]
  refine ⟨m, ?_, ?_⟩
  · rwa [hD] at hm
  · intro f
    simpa only [hD, nonarchimedean_gaussianIndex_inverse hNondiscrete ψ hu hc hn] using hma f

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanDiagonalLevi.Construction
