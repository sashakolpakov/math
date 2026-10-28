import OAI.RepresentationTheory.Weil.Local.NormalizedFresnel

/-! # Linear Oscillator Hom -/

namespace OAI.RepresentationTheory.Weil.Local.LinearOscillatorHom.Construction

noncomputable section

/-! Multiplicativity of the positive-normalized linear oscillator lifts. -/

open _root_.MeasureTheory

theorem determinantUnit_mul {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {n : ℕ} (A B : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    FunctionsMetaplectic.Construction.determinantUnit k (A * B) = FunctionsMetaplectic.Construction.determinantUnit k A * FunctionsMetaplectic.Construction.determinantUnit k B := by
  apply Units.ext
  exact Matrix.det_mul A.val B.val

theorem linearOscillator_one
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (n : ℕ)
    (ψ : AddChar k ℂ) : LinearIntertwiner.Construction.linearOscillator ψ (1 : FunctionsMetaplectic.Construction.GeneralLinear k n) = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact (GenerationSymplectic.Construction.leviHom (k := k) (n := n)).map_one
  · apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    rw [LinearIntertwiner.Construction.linearOscillator_apply]
    have hdet : FunctionsMetaplectic.Construction.determinantUnit k (1 : FunctionsMetaplectic.Construction.GeneralLinear k n) = 1 := by
      apply Units.ext
      simp [FunctionsMetaplectic.Construction.determinantUnit]
    simp [hdet, FunctionsMetaplectic.Construction.localModulus_one]

theorem linearOscillator_mul
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (A B : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    LinearIntertwiner.Construction.linearOscillator ψ (A * B) = LinearIntertwiner.Construction.linearOscillator ψ A * LinearIntertwiner.Construction.linearOscillator ψ B := by
  apply Subtype.ext
  apply Prod.ext
  · exact (GenerationSymplectic.Construction.leviHom (k := k) (n := n)).map_mul A B
  · apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    change ((LinearIntertwiner.Construction.linearOscillator ψ (A * B)).val.2 f).val x =
      ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 ((LinearIntertwiner.Construction.linearOscillator ψ B).val.2 f)).val x
    rw [LinearIntertwiner.Construction.linearOscillator_apply, LinearIntertwiner.Construction.linearOscillator_apply, LinearIntertwiner.Construction.linearOscillator_apply,
      determinantUnit_mul, FunctionsMetaplectic.Construction.localModulus_mul, Real.sqrt_mul (FunctionsMetaplectic.Construction.localModulus_pos k _).le]
    simp only [mul_inv_rev, Complex.ofReal_mul, Units.val_mul,
      Matrix.mulVec_mulVec]
    ring

def linearOscillatorHom
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (n : ℕ)
    (ψ : AddChar k ℂ) : FunctionsMetaplectic.Construction.GeneralLinear k n →* FunctionsMetaplectic.Construction.Oscillator k n ψ where
  toFun := LinearIntertwiner.Construction.linearOscillator ψ
  map_one' := linearOscillator_one n ψ
  map_mul' := linearOscillator_mul ψ

theorem linear_commutator_mem_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (A B : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    LinearIntertwiner.Construction.linearOscillator ψ (A * B * A⁻¹ * B⁻¹) ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
  change linearOscillatorHom n ψ (A * B * A⁻¹ * B⁻¹) ∈ _
  simp only [map_mul, map_inv]
  apply Subgroup.subset_closure
  left
  exact ⟨linearOscillatorHom n ψ A, linearOscillatorHom n ψ B, rfl⟩

end

end OAI.RepresentationTheory.Weil.Local.LinearOscillatorHom.Construction
