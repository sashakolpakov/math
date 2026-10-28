import OAI.RepresentationTheory.Weil.Local.TransposeSubstitution

/-! # Test Fourier Normal Form -/

namespace OAI.RepresentationTheory.Weil.Local.TestFourierNormalForm.Construction

noncomputable section

section

/-! Exact relations between the concrete test-space generators. -/

open _root_.Matrix _root_.MeasureTheory

theorem fourierIntegral_linearOscillator_transpose
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f).val x =
      ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k (TransposeSubstitution.Construction.transposeGeneralLinear A)⁻¹)))⁻¹ : ℂ) *
        FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val (A.val.transpose *ᵥ x) := by
  let d := FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)
  have hd : 0 < d := FunctionsMetaplectic.Construction.localModulus_pos k _
  have hf : ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f).val =
      ((Real.sqrt d)⁻¹ : ℂ) • FunctionsMetaplectic.Construction.substitutionOperator A f.val := funext (LinearIntertwiner.Construction.linearOscillator_apply ψ A f)
  rw [hf, FunctionsMetaplectic.Construction.fourierIntegral_smul, Pi.smul_apply, TransposeSubstitution.Construction.fourierIntegral_transpose_substitution ψ μ A,
    Complex.real_smul, FourierLinearSubstitution.Construction.determinantUnit_inv, TransposeSubstitution.Construction.determinantUnit_transpose, FunctionsMetaplectic.Construction.localModulus_inv, Real.sqrt_inv]
  simp only [smul_eq_mul, Complex.ofReal_inv, inv_inv]
  change (Real.sqrt d : ℂ)⁻¹ * ((d : ℂ) * _) = (Real.sqrt d : ℂ) * _
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have he : (Real.sqrt d)⁻¹ * d = Real.sqrt d := by
    calc
      _ = (Real.sqrt d)⁻¹ * (Real.sqrt d * Real.sqrt d) :=
        congrArg (fun r : ℝ => (Real.sqrt d)⁻¹ * r) (Real.mul_self_sqrt hd.le).symm
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, he]

theorem testFourier_linear_transpose
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (F : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (hF : ∀ f x, (F f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val x)
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    F ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f) =
      (LinearIntertwiner.Construction.linearOscillator ψ (TransposeSubstitution.Construction.transposeGeneralLinear A)⁻¹).val.2 (F f) := by
  apply Subtype.ext
  funext x
  rw [hF, LinearIntertwiner.Construction.linearOscillator_apply, inv_inv, hF]
  exact fourierIntegral_linearOscillator_transpose ψ μ A f x

variable {k : Type} [NormedField k] {n : ℕ} (ψ : AddChar k ℂ)
  (hs : ∀ (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n),
    FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n)

theorem testQuadratic_add (B C : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    QuadraticIntertwiner.Construction.testQuadratic ψ hs B (QuadraticIntertwiner.Construction.testQuadratic ψ hs C f) = QuadraticIntertwiner.Construction.testQuadratic ψ hs (B + C) f := by
  apply Subtype.ext
  exact Generators.Construction.quadraticOperator_comp ψ B C f.val

theorem testQuadratic_linear_congruence
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    QuadraticIntertwiner.Construction.testQuadratic ψ hs B ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f) =
      (LinearIntertwiner.Construction.linearOscillator ψ A).val.2 (QuadraticIntertwiner.Construction.testQuadratic ψ hs (A.val.transpose * B * A.val) f) := by
  apply Subtype.ext
  funext x
  change ψ (FunctionsMetaplectic.Construction.quadratic B x) * ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f).val x = _
  rw [LinearIntertwiner.Construction.linearOscillator_apply, LinearIntertwiner.Construction.linearOscillator_apply]
  change _ = _ * (ψ (FunctionsMetaplectic.Construction.quadratic (A.val.transpose * B * A.val) (A⁻¹.val *ᵥ x)) * f.val (A⁻¹.val *ᵥ x))
  rw [TransposeSubstitution.Construction.quadratic_matrix_congruence, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, one_mulVec]
  ring

theorem testLinear_quadratic_congruence
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (LinearIntertwiner.Construction.linearOscillator ψ A).val.2 (QuadraticIntertwiner.Construction.testQuadratic ψ hs B f) =
      QuadraticIntertwiner.Construction.testQuadratic ψ hs (A⁻¹.val.transpose * B * A⁻¹.val) ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f) := by
  apply Subtype.ext
  funext x
  change ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 (QuadraticIntertwiner.Construction.testQuadratic ψ hs B f)).val x =
    ψ (FunctionsMetaplectic.Construction.quadratic (A⁻¹.val.transpose * B * A⁻¹.val) x) * ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f).val x
  rw [LinearIntertwiner.Construction.linearOscillator_apply, LinearIntertwiner.Construction.linearOscillator_apply, TransposeSubstitution.Construction.quadratic_matrix_congruence]
  change _ * (ψ (FunctionsMetaplectic.Construction.quadratic B (A⁻¹.val *ᵥ x)) * f.val (A⁻¹.val *ᵥ x)) = _
  ring

end

/-! Multiplication of concrete Fourier normal forms. -/

open _root_.Matrix _root_.MeasureTheory

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
  (ψ : AddChar k ℂ)
  (hs : ∀ (B : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n),
    FunctionsMetaplectic.Construction.quadraticOperator ψ B f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n)
  (F : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n)

def testFourierNormalForm (P : Matrix (Fin n) (Fin n) k) (B : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (Q : Matrix (Fin n) (Fin n) k) : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n :=
  QuadraticIntertwiner.Construction.testQuadratic ψ hs P * (LinearIntertwiner.Construction.linearOscillator ψ B).val.2 * F * QuadraticIntertwiner.Construction.testQuadratic ψ hs Q

theorem testFourierNormalForm_apply (P : Matrix (Fin n) (Fin n) k) (B : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (Q : Matrix (Fin n) (Fin n) k) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    testFourierNormalForm ψ hs F P B Q f =
      QuadraticIntertwiner.Construction.testQuadratic ψ hs P ((LinearIntertwiner.Construction.linearOscillator ψ B).val.2 (F (QuadraticIntertwiner.Construction.testQuadratic ψ hs Q f))) := rfl

theorem testFourierNormalForm_product
    (μ : Measure k) [μ.IsAddHaarMeasure]
    (hF : ∀ f x, (F f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val x)
    (P Q P' Q' : Matrix (Fin n) (Fin n) k) (B B' N : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (hN : N.val = B'.val.transpose * (Q + P') * B'.val)
    (Γ : ℂ)
    (hrel : ∀ f, F (QuadraticIntertwiner.Construction.testQuadratic ψ hs N.val (F f)) =
      Γ • QuadraticIntertwiner.Construction.testQuadratic ψ hs (-N⁻¹.val)
        ((LinearIntertwiner.Construction.linearOscillator ψ N).val.2 (F (QuadraticIntertwiner.Construction.testQuadratic ψ hs (-N⁻¹.val) f))))
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    let C := B * (TransposeSubstitution.Construction.transposeGeneralLinear B')⁻¹
    testFourierNormalForm ψ hs F P B Q (testFourierNormalForm ψ hs F P' B' Q' f) =
      Γ • testFourierNormalForm ψ hs F
        (P + C⁻¹.val.transpose * (-N⁻¹.val) * C⁻¹.val) (C * N) (-N⁻¹.val + Q') f := by
  let C := B * (TransposeSubstitution.Construction.transposeGeneralLinear B')⁻¹
  have hL (A D : FunctionsMetaplectic.Construction.GeneralLinear k n) (g : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
      (LinearIntertwiner.Construction.linearOscillator ψ A).val.2 ((LinearIntertwiner.Construction.linearOscillator ψ D).val.2 g) =
        (LinearIntertwiner.Construction.linearOscillator ψ (A * D)).val.2 g := by
    exact congrArg (fun a : FunctionsMetaplectic.Construction.Oscillator k n ψ => a.val.2 g) (LinearOscillatorHom.Construction.linearOscillator_mul ψ A D).symm
  simp only [testFourierNormalForm_apply]
  rw [testQuadratic_add, testQuadratic_linear_congruence ψ hs B' (Q + P'), ← hN,
    testFourier_linear_transpose ψ μ F hF, hL, hrel, map_smul, map_smul,
    testLinear_quadratic_congruence, testQuadratic_add, hL, testQuadratic_add]

end

end OAI.RepresentationTheory.Weil.Local.TestFourierNormalForm.Construction
