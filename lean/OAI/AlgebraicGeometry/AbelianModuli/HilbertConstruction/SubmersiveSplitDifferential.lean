import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersivePolynomialSplit

/-! # Submersive Split Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitDifferential

noncomputable section

/-! The polynomial variable split preserves partial derivatives in the selected Jacobian variables. -/

universe u v w

variable (R : Type u) [CommRing R] {ι : Type v} {σ : Type w}
variable (m : σ → ι) (hm : Function.Injective m)

theorem submersivePolynomialSplit_pderiv (j : σ) (p : MvPolynomial ι R) :
    MvPolynomial.pderiv j (SubmersivePolynomialSplit.submersivePolynomialSplit R m hm p) =
      SubmersivePolynomialSplit.submersivePolynomialSplit R m hm (MvPolynomial.pderiv (m j) p) := by
  change MvPolynomial.pderiv j
    (MvPolynomial.sumAlgEquiv R σ (SubmersivePolynomialSplit.UnselectedVariables m)
      (MvPolynomial.rename (SubmersivePolynomialSplit.injectionSumComplementEquiv m hm).symm p)) =
    MvPolynomial.sumAlgEquiv R σ (SubmersivePolynomialSplit.UnselectedVariables m)
      (MvPolynomial.rename (SubmersivePolynomialSplit.injectionSumComplementEquiv m hm).symm (MvPolynomial.pderiv (m j) p))
  rw [MvPolynomial.pderiv_sumAlgEquiv]
  apply congrArg (MvPolynomial.sumAlgEquiv R σ (SubmersivePolynomialSplit.UnselectedVariables m))
  have h := MvPolynomial.pderiv_rename (SubmersivePolynomialSplit.injectionSumComplementEquiv m hm).symm.injective (m j) p
  rw [SubmersivePolynomialSplit.injectionSumComplementEquiv_symm_selected] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersiveSplitDifferential
