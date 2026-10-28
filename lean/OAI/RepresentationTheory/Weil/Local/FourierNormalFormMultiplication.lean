import OAI.RepresentationTheory.Weil.Local.SymmetricMatrixOperations

/-! # Fourier Normal Form Multiplication -/

namespace OAI.RepresentationTheory.Weil.Local.FourierNormalFormMultiplication.Construction

noncomputable section

/-! The symplectic product corresponding to the concrete Fresnel operator relation. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

theorem fourierNormalForm_product_formula
    (P Q P' Q' : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (B B' N : FunctionsMetaplectic.Construction.GeneralLinear k n)
    (hN : N.val = B'.val.transpose * (Q.val + P'.val) * B'.val) (hNs : N.val.IsSymm) :
    let C := B * (TransposeSubstitution.Construction.transposeGeneralLinear B')⁻¹
    let S := SymmetricMatrixOperations.Construction.symmetricNegativeInverse N hNs
    FourierNormalForm.Construction.fourierNormalForm P B Q * FourierNormalForm.Construction.fourierNormalForm P' B' Q' =
      FourierNormalForm.Construction.fourierNormalForm (SymmetricMatrixOperations.Construction.symmetricAdd P (SymmetricMatrixOperations.Construction.symmetricCongruence C⁻¹.val S))
        (C * N) (SymmetricMatrixOperations.Construction.symmetricAdd S Q') := by
  let C := B * (TransposeSubstitution.Construction.transposeGeneralLinear B')⁻¹
  let S := SymmetricMatrixOperations.Construction.symmetricNegativeInverse N hNs
  have hNsym : SymmetricMatrixOperations.Construction.symmetricCongruence B'.val (SymmetricMatrixOperations.Construction.symmetricAdd Q P') = ⟨N.val, hNs⟩ := Subtype.ext hN.symm
  have hL (A D : FunctionsMetaplectic.Construction.GeneralLinear k n) : Generators.Construction.leviSymplectic A * Generators.Construction.leviSymplectic D = Generators.Construction.leviSymplectic (A * D) :=
    ((GenerationSymplectic.Construction.leviHom (k := k) (n := n)).map_mul A D).symm
  change _ = FourierNormalForm.Construction.fourierNormalForm (SymmetricMatrixOperations.Construction.symmetricAdd P (SymmetricMatrixOperations.Construction.symmetricCongruence C⁻¹.val S)) (C * N) (SymmetricMatrixOperations.Construction.symmetricAdd S Q')
  unfold FourierNormalForm.Construction.fourierNormalForm
  simp only [mul_assoc]
  rw [← mul_assoc (Generators.Construction.quadraticSymplectic Q) (Generators.Construction.quadraticSymplectic P'), SymmetricMatrixOperations.Construction.quadraticSymplectic_add,
    ← mul_assoc (Generators.Construction.quadraticSymplectic (SymmetricMatrixOperations.Construction.symmetricAdd Q P')) (Generators.Construction.leviSymplectic B'),
    SymmetricMatrixOperations.Construction.quadraticSymplectic_levi_congruence, hNsym]
  simp only [mul_assoc]
  rw [← mul_assoc (Generators.Construction.weylSymplectic k n) (Generators.Construction.leviSymplectic B'), SymmetricMatrixOperations.Construction.weyl_levi_transpose]
  simp only [mul_assoc]
  rw [← mul_assoc (Generators.Construction.leviSymplectic B) (Generators.Construction.leviSymplectic (TransposeSubstitution.Construction.transposeGeneralLinear B')⁻¹), hL,
    ← mul_assoc (Generators.Construction.weylSymplectic k n) (Generators.Construction.quadraticSymplectic ⟨N.val, hNs⟩),
    ← mul_assoc (Generators.Construction.weylSymplectic k n * Generators.Construction.quadraticSymplectic ⟨N.val, hNs⟩) (Generators.Construction.weylSymplectic k n),
    SymmetricMatrixOperations.Construction.weyl_quadratic_weyl]
  change Generators.Construction.quadraticSymplectic P * (Generators.Construction.leviSymplectic C *
    (FourierNormalForm.Construction.fourierNormalForm S N S * Generators.Construction.quadraticSymplectic Q')) = _
  unfold FourierNormalForm.Construction.fourierNormalForm
  simp only [mul_assoc]
  rw [← mul_assoc (Generators.Construction.leviSymplectic C) (Generators.Construction.quadraticSymplectic S), SymmetricMatrixOperations.Construction.levi_quadraticSymplectic_congruence]
  simp only [mul_assoc]
  rw [← mul_assoc (Generators.Construction.quadraticSymplectic P) (Generators.Construction.quadraticSymplectic (SymmetricMatrixOperations.Construction.symmetricCongruence C⁻¹.val S)),
    SymmetricMatrixOperations.Construction.quadraticSymplectic_add, ← mul_assoc (Generators.Construction.leviSymplectic C) (Generators.Construction.leviSymplectic N), hL,
    SymmetricMatrixOperations.Construction.quadraticSymplectic_add]

end

end OAI.RepresentationTheory.Weil.Local.FourierNormalFormMultiplication.Construction
