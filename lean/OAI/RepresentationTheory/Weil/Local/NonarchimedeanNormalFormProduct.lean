import OAI.RepresentationTheory.Weil.Local.TestFourierNormalForm
import OAI.RepresentationTheory.Weil.Local.FourierNormalFormMultiplication
import OAI.RepresentationTheory.Weil.Local.GeneralFresnelOperator
import OAI.RepresentationTheory.Weil.Local.GaussianNormalFormFactors

/-! # Nonarchimedean Normal Form Product -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalFormProduct.Construction

noncomputable section

/-! Exact products of normalized Fourier operators, with the Gaussian determinant factor. -/

open _root_.Matrix _root_.MeasureTheory

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  [SecondCountableTopology k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

theorem exists_nonarchimedean_normalForm_product {n : ℕ}
    (F : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (hF : ∀ f x, (F f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x)
    (P Q P' Q' : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B B' : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (hprod : FourierNormalForm.Construction.fourierNormalForm P B Q * FourierNormalForm.Construction.fourierNormalForm P' B' Q' ∈ FourierBigCell.Construction.fourierBigCell k n) :
    let χ := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns
    let R := TestFourierNormalForm.Construction.testFourierNormalForm ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) F
    ∃ (P'' Q'' : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B'' : FunctionsMetaplectic.Construction.GeneralLinear k n) (Γ : ℂ),
      FourierNormalForm.Construction.fourierNormalForm P B Q * FourierNormalForm.Construction.fourierNormalForm P' B' Q' = FourierNormalForm.Construction.fourierNormalForm P'' B'' Q'' ∧
      Γ ^ 2 * (χ (FunctionsMetaplectic.Construction.determinantUnit k B'')).val =
        FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) *
          (χ (FunctionsMetaplectic.Construction.determinantUnit k B)).val * (χ (FunctionsMetaplectic.Construction.determinantUnit k B')).val ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, R P.val B Q.val (R P'.val B' Q'.val f) =
        Γ • R P''.val B'' Q''.val f := by
  let χ := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns
  let R := TestFourierNormalForm.Construction.testFourierNormalForm ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) F
  have hm := FourierNormalForm.Construction.fourierNormalForm_product_middle_nonsingular P Q P' Q' B B' hprod
  obtain ⟨M, hM⟩ := (Matrix.isUnit_iff_isUnit_det (Q.val + P'.val)).mpr (isUnit_iff_ne_zero.mpr hm)
  let N := TransposeSubstitution.Construction.transposeGeneralLinear B' * M * B'
  have hN : N.val = B'.val.transpose * (Q.val + P'.val) * B'.val := by
    change B'.val.transpose * M.val * B'.val = _
    rw [hM]
  have hNs : N.val.IsSymm := by
    rw [hN]
    exact (SymmetricMatrixOperations.Construction.symmetricCongruence B'.val (SymmetricMatrixOperations.Construction.symmetricAdd Q P')).property
  obtain ⟨Γ, hΓ, hrel⟩ := GeneralFresnelOperator.Construction.exists_nonarchimedean_general_fourier_relation hnd ψ hu hc hn hns N hNs F hF
  let C := B * (TransposeSubstitution.Construction.transposeGeneralLinear B')⁻¹
  let S := SymmetricMatrixOperations.Construction.symmetricNegativeInverse N hNs
  refine ⟨SymmetricMatrixOperations.Construction.symmetricAdd P (SymmetricMatrixOperations.Construction.symmetricCongruence C⁻¹.val S), SymmetricMatrixOperations.Construction.symmetricAdd S Q', C * N, Γ,
    FourierNormalFormMultiplication.Construction.fourierNormalForm_product_formula P Q P' Q' B B' N hN hNs, ?_, ?_⟩
  · change Γ ^ 2 * (χ (FunctionsMetaplectic.Construction.determinantUnit k (C * N))).val = _
    rw [hΓ, mul_assoc, ← Units.val_mul]
    have he := GaussianNormalFormFactors.Construction.gaussianSquareCharacter_normalForm_product hnd ψ hu hc hn hns B B' N
    change χ (FunctionsMetaplectic.Construction.determinantUnit k N) * χ (FunctionsMetaplectic.Construction.determinantUnit k (C * N)) =
      χ (FunctionsMetaplectic.Construction.determinantUnit k B) * χ (FunctionsMetaplectic.Construction.determinantUnit k B') at he
    rw [he, Units.val_mul, ← mul_assoc]
  · let : (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
      NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hnd ψ hu hc hn
    intro f
    exact TestFourierNormalForm.Construction.testFourierNormalForm_product ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) F
      (FunctionsMetaplectic.Construction.selfDualMeasure k ψ) hF P.val Q.val P'.val Q'.val B B' N hN Γ hrel f

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalFormProduct.Construction
