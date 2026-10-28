import OAI.RepresentationTheory.Weil.Local.NonarchimedeanDiagonalLevi
import OAI.RepresentationTheory.Weil.Local.SquareDeterminantLift

/-! # Nonarchimedean Levi -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanLevi.Construction

noncomputable section

/-! The exact bare Levi generator at every nonarchimedean place and every determinant. -/

open _root_.Matrix

theorem exists_nonarchimedean_coordinate_levi_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1) (j : Fin n) (b : kˣ) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic k n ψ, FunctionsMetaplectic.Construction.metaplecticProjection k n ψ m = Generators.Construction.leviSymplectic (SpecialLinearCommutators.Construction.coordinateDiagonal j b) ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
        FunctionsMetaplectic.Construction.weilRepresentation k n ψ m f = (FunctionsMetaplectic.Construction.gaussianIndex k ψ b.val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) •
          (LinearIntertwiner.Construction.linearOscillator ψ (SpecialLinearCommutators.Construction.coordinateDiagonal j b)).val.2 f := by
  classical
  let a : Fin n → kˣ := fun i => if i = j then b else 1
  have hD : DiagonalAlgebra.Construction.diagonalGeneralLinear a = SpecialLinearCommutators.Construction.coordinateDiagonal j b := by
    apply Units.ext
    change diagonal (fun i => (a i).val) = diagonal (fun i => if i = j then b.val else 1)
    congr 1
    funext i
    dsimp [a]
    split_ifs <;> rfl
  obtain ⟨m, hm, hop⟩ := NonarchimedeanDiagonalLevi.Construction.exists_nonarchimedean_diagonal_levi_metaplectic hNondiscrete ψ hu hc hn a
  have hγ : FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ≠ 0 :=
    FunctionsMetaplectic.Construction.phase_ne_zero (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hn 1 one_ne_zero).2
  have hratio : (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n =
      FunctionsMetaplectic.Construction.gaussianIndex k ψ b.val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 := by
    have he (i : Fin n) : FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 =
        if i = j then FunctionsMetaplectic.Construction.gaussianIndex k ψ b.val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 else 1 := by
      dsimp [a]
      split_ifs
      · rfl
      · exact div_self hγ
    calc
      _ = ∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 := by
        rw [Finset.prod_div_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = _ := by simp only [he, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  refine ⟨m, ?_, fun f => ?_⟩
  · rwa [hD] at hm
  · simpa only [hD, hratio] using hop f

theorem exists_nonarchimedean_levi_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ) (hn : 0 < n)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hψ : ∃ t : k, ψ t ≠ 1) (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic k n ψ, FunctionsMetaplectic.Construction.metaplecticProjection k n ψ m = Generators.Construction.leviSymplectic A ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
        (FunctionsMetaplectic.Construction.weilRepresentation k n ψ m f).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex k ψ (FunctionsMetaplectic.Construction.determinantUnit k A) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) *
            ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) * f.val (A⁻¹.val *ᵥ x) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let j : Fin n := ⟨0, hn⟩
  let D := SpecialLinearCommutators.Construction.coordinateDiagonal j (FunctionsMetaplectic.Construction.determinantUnit k A)
  let S := A * D⁻¹
  have hDdet : FunctionsMetaplectic.Construction.determinantUnit k D = FunctionsMetaplectic.Construction.determinantUnit k A := ComplexLevi.Construction.coordinateDiagonal_determinant j _
  have hSdet : S.val.det = 1 := by
    change (FunctionsMetaplectic.Construction.determinantUnit k (A * D⁻¹)).val = 1
    rw [LinearOscillatorHom.Construction.determinantUnit_mul, FourierLinearSubstitution.Construction.determinantUnit_inv, hDdet, mul_inv_cancel, Units.val_one]
  have hSD : S * D = A := by dsimp [S]; rw [mul_assoc, inv_mul_cancel, mul_one]
  let mS := SpecialLinearCommutators.Construction.specialLinearMetaplectic hNondiscrete ψ S hSdet
  obtain ⟨mD, hmD, hmDa⟩ := exists_nonarchimedean_coordinate_levi_metaplectic hNondiscrete ψ hu hc hψ j
    (FunctionsMetaplectic.Construction.determinantUnit k A)
  have hmSop (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : FunctionsMetaplectic.Construction.weilRepresentation k n ψ mS f = (LinearIntertwiner.Construction.linearOscillator ψ S).val.2 f := rfl
  have hL : LinearIntertwiner.Construction.linearOscillator ψ S * LinearIntertwiner.Construction.linearOscillator ψ D = LinearIntertwiner.Construction.linearOscillator ψ A := by
    rw [← LinearOscillatorHom.Construction.linearOscillator_mul, hSD]
  refine ⟨mS * mD, ?_, fun f x => ?_⟩
  · rw [map_mul, SpecialLinearCommutators.Construction.specialLinearMetaplectic_projection, hmD]
    exact congrArg (OscillatorProjection.Construction.oscillatorProjection k n ψ) hL
  · change (FunctionsMetaplectic.Construction.weilRepresentation k n ψ mS (FunctionsMetaplectic.Construction.weilRepresentation k n ψ mD f)).val x = _
    rw [hmSop, hmDa, map_smul]
    have he := congrArg (fun b : FunctionsMetaplectic.Construction.Oscillator k n ψ => b.val.2 f) hL
    change (LinearIntertwiner.Construction.linearOscillator ψ S).val.2 ((LinearIntertwiner.Construction.linearOscillator ψ D).val.2 f) = (LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f at he
    change (FunctionsMetaplectic.Construction.gaussianIndex k ψ (FunctionsMetaplectic.Construction.determinantUnit k A) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) *
      ((LinearIntertwiner.Construction.linearOscillator ψ S).val.2 ((LinearIntertwiner.Construction.linearOscillator ψ D).val.2 f)).val x = _
    rw [he, LinearIntertwiner.Construction.linearOscillator_apply]
    ring

def nonarchimedeanLinearMetaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ) (hn : 0 < n)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hψ : ∃ t : k, ψ t ≠ 1) (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    FunctionsMetaplectic.Construction.Metaplectic k n ψ :=
  Classical.choose (exists_nonarchimedean_levi_metaplectic hNondiscrete n hn ψ hu hc hψ A)

theorem nonarchimedeanLinearMetaplectic_projection
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ) (hn : 0 < n)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hψ : ∃ t : k, ψ t ≠ 1) (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (nonarchimedeanLinearMetaplectic hNondiscrete n hn ψ hu hc hψ A) =
      Generators.Construction.leviSymplectic A :=
  (Classical.choose_spec (exists_nonarchimedean_levi_metaplectic hNondiscrete n hn ψ hu hc hψ A)).1

theorem nonarchimedeanLinearMetaplectic_apply
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ) (hn : 0 < n)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hψ : ∃ t : k, ψ t ≠ 1) (A : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    (FunctionsMetaplectic.Construction.weilRepresentation k n ψ (nonarchimedeanLinearMetaplectic hNondiscrete n hn ψ hu hc hψ A) f).val x =
      (FunctionsMetaplectic.Construction.gaussianIndex k ψ (FunctionsMetaplectic.Construction.determinantUnit k A) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) *
        ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) * f.val (A⁻¹.val *ᵥ x) :=
  (Classical.choose_spec (exists_nonarchimedean_levi_metaplectic hNondiscrete n hn ψ hu hc hψ A)).2 f x

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanLevi.Construction
