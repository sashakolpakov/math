import OAI.RepresentationTheory.Weil.Local.FourierLinearSubstitution

/-! # Symmetric Square Lift -/

namespace OAI.RepresentationTheory.Weil.Local.SymmetricSquareLift.Construction

noncomputable section

/-! Positive normalized lifts of symmetric squares lie in the intrinsic bare cover. -/

open _root_.Matrix _root_.MeasureTheory

theorem weyl_levi_symmetric
    {k : Type} [Field k] {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (hA : A.val.IsSymm) :
    Generators.Construction.weylSymplectic k n * Generators.Construction.leviSymplectic A = Generators.Construction.leviSymplectic A⁻¹ * Generators.Construction.weylSymplectic k n := by
  apply Subtype.ext
  change (Generators.Construction.weylSymplectic k n).val * (Generators.Construction.leviSymplectic A).val =
    (Generators.Construction.leviSymplectic A⁻¹).val * (Generators.Construction.weylSymplectic k n).val
  simp [Generators.Construction.weylSymplectic, Generators.Construction.leviSymplectic, Matrix.fromBlocks_multiply, hA.eq, hA.inv.eq]

theorem fourierOscillator_linear_symmetric
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (w : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (hF : ∀ f x, (w.val.2 f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val x)
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (hA : A.val.IsSymm) :
    w * LinearIntertwiner.Construction.linearOscillator ψ A = LinearIntertwiner.Construction.linearOscillator ψ A⁻¹ * w := by
  apply Subtype.ext
  apply Prod.ext
  · change w.val.1 * Generators.Construction.leviSymplectic A = Generators.Construction.leviSymplectic A⁻¹ * w.val.1
    have hw1 : w.val.1 = Generators.Construction.weylSymplectic k n := hw
    rw [hw1]
    exact weyl_levi_symmetric A hA
  · apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext x
    change (w.val.2 ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f)).val x =
      ((LinearIntertwiner.Construction.linearOscillator ψ A⁻¹).val.2 (w.val.2 f)).val x
    rw [hF, LinearIntertwiner.Construction.linearOscillator_apply, inv_inv, hF]
    exact FourierLinearSubstitution.Construction.fourierIntegral_linearOscillator_symmetric ψ μ A hA f x

theorem linearOscillator_symmetric_square_mem
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (w : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hw : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (hF : ∀ f x, (w.val.2 f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val x)
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (hA : A.val.IsSymm) :
    LinearIntertwiner.Construction.linearOscillator ψ (A * A) ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
  have hAi : (A⁻¹.val).IsSymm := by simpa only [Matrix.coe_units_inv] using hA.inv
  have h := fourierOscillator_linear_symmetric ψ μ w hw hF A⁻¹ hAi
  rw [inv_inv] at h
  have hinv : LinearIntertwiner.Construction.linearOscillator ψ A⁻¹ = (LinearIntertwiner.Construction.linearOscillator ψ A)⁻¹ :=
    (LinearOscillatorHom.Construction.linearOscillatorHom n ψ).map_inv A
  rw [hinv] at h
  have hcomm : LinearIntertwiner.Construction.linearOscillator ψ A * w * (LinearIntertwiner.Construction.linearOscillator ψ A)⁻¹ * w⁻¹ =
      LinearIntertwiner.Construction.linearOscillator ψ (A * A) := by
    rw [mul_assoc (LinearIntertwiner.Construction.linearOscillator ψ A) w, h, ← mul_assoc, mul_inv_cancel_right,
      LinearOscillatorHom.Construction.linearOscillator_mul]
  apply Subgroup.subset_closure
  left
  exact ⟨LinearIntertwiner.Construction.linearOscillator ψ A, w, hcomm⟩

end

end OAI.RepresentationTheory.Weil.Local.SymmetricSquareLift.Construction
