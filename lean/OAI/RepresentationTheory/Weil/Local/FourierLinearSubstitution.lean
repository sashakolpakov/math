import OAI.RepresentationTheory.Weil.Local.LinearOscillatorHom

/-! # Fourier Linear Substitution -/

namespace OAI.RepresentationTheory.Weil.Local.FourierLinearSubstitution.Construction

noncomputable section

/-! Fourier covariance under symmetric normalized linear substitutions. -/

open _root_.Matrix _root_.MeasureTheory
open scoped Classical NNReal

theorem determinantUnit_inv
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n) : FunctionsMetaplectic.Construction.determinantUnit k A⁻¹ = (FunctionsMetaplectic.Construction.determinantUnit k A)⁻¹ := by
  simp [FunctionsMetaplectic.Construction.determinantUnit]

theorem integral_matrix_inverse
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (μ : Measure k) [μ.IsAddHaarMeasure] (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    (∫ x, f (A⁻¹.val *ᵥ x) ∂Measure.pi (fun _ : Fin n => μ)) =
      (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℝ) • ∫ x, f x ∂Measure.pi (fun _ : Fin n => μ) := by
  let e := LinearSubstitution.Construction.positionAddEquiv A⁻¹
  have hm := DeterminantMeasure.Construction.map_matrix_haar_eq_smul μ (FunctionsMetaplectic.Construction.determinantUnit k A⁻¹).ne_zero
  have hd : (det (A⁻¹ : FunctionsMetaplectic.Construction.GeneralLinear k n).val)⁻¹ = det A.val := by
    change ((FunctionsMetaplectic.Construction.determinantUnit k A⁻¹).val)⁻¹ = (FunctionsMetaplectic.Construction.determinantUnit k A).val
    rw [determinantUnit_inv, Units.val_inv_eq_inv_val, inv_inv]
  rw [hd] at hm
  have hi := integral_map_equiv (μ := Measure.pi (fun _ : Fin n => μ)) e.toHomeomorph.toMeasurableEquiv f
  change (∫ x, f x ∂Measure.map (Matrix.toLin' (A⁻¹ : FunctionsMetaplectic.Construction.GeneralLinear k n).val)
    (Measure.pi (fun _ : Fin n => μ))) = _ at hi
  rw [hm, integral_smul_measure] at hi
  simp only [ENNReal.coe_toReal] at hi
  have hmod : (DeterminantMeasure.Construction.haarModulus k (det A.val) : ℝ) = FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) :=
    congrArg (fun r : ℝ≥0 => (r : ℝ)) (DeterminantMeasure.Construction.haarModulus_unit k (FunctionsMetaplectic.Construction.determinantUnit k A))
  rw [hmod] at hi
  exact hi.symm

theorem fourierIntegral_symmetric_substitution
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (hA : A.val.IsSymm) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) (FunctionsMetaplectic.Construction.substitutionOperator A f) x =
      (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℝ) •
        FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f (A.val *ᵥ x) := by
  have h := integral_matrix_inverse μ A (fun y => f y * ψ (-FunctionsMetaplectic.Construction.dot (A.val *ᵥ x) y))
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [FunctionsMetaplectic.Construction.substitutionOperator_apply]
    congr 2
    have heq : FunctionsMetaplectic.Construction.dot (A.val *ᵥ x) (A⁻¹.val *ᵥ y) = FunctionsMetaplectic.Construction.dot x y := by
      change (A.val *ᵥ x) ⬝ᵥ (A⁻¹.val *ᵥ y) = x ⬝ᵥ y
      rw [← Matrix.vecMul_transpose, hA.eq, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    exact congrArg Neg.neg heq.symm

theorem fourierIntegral_linearOscillator_symmetric
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (hA : A.val.IsSymm) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f).val x =
      ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A⁻¹)))⁻¹ : ℂ) *
        FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val (A.val *ᵥ x) := by
  let d := FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)
  have hd : 0 < d := FunctionsMetaplectic.Construction.localModulus_pos k _
  have hf : ((LinearIntertwiner.Construction.linearOscillator ψ A).val.2 f).val =
      ((Real.sqrt d)⁻¹ : ℂ) • FunctionsMetaplectic.Construction.substitutionOperator A f.val := funext (LinearIntertwiner.Construction.linearOscillator_apply ψ A f)
  rw [hf, FunctionsMetaplectic.Construction.fourierIntegral_smul, Pi.smul_apply, fourierIntegral_symmetric_substitution ψ μ A hA,
    Complex.real_smul, determinantUnit_inv, FunctionsMetaplectic.Construction.localModulus_inv, Real.sqrt_inv]
  simp only [smul_eq_mul, Complex.ofReal_inv, inv_inv]
  change (Real.sqrt d : ℂ)⁻¹ * ((d : ℂ) * _) = (Real.sqrt d : ℂ) * _
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have he : (Real.sqrt d)⁻¹ * d = Real.sqrt d := by
    calc
      _ = (Real.sqrt d)⁻¹ * (Real.sqrt d * Real.sqrt d) :=
        congrArg (fun r : ℝ => (Real.sqrt d)⁻¹ * r) (Real.mul_self_sqrt hd.le).symm
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, he]

end

end OAI.RepresentationTheory.Weil.Local.FourierLinearSubstitution.Construction
