import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedRename
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.PolynomialCoefficients

/-! # Iterated Polynomial Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPolynomialCoefficients.GradedHilbert

noncomputable section

/-! Coefficients in an iterated polynomial ring preserve the degree control needed for syzygy generators. -/

open _root_.MvPolynomial

variable {K σ ι : Type*} [Field K]

theorem coeff_coeff_sumAlgEquiv (p : MvPolynomial (ι ⊕ σ) K)
    (a : ι →₀ ℕ) (b : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff (sumAlgEquiv K ι σ p) a) b =
      AddMonoidAlgebra.coeff p (a.sumElim b) := by
  simp [sumAlgEquiv, AddMonoidAlgebra.curryAlgEquiv,
    AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv]

theorem naturalWeight_sumElim (w : ι ⊕ σ → ℕ) (a : ι →₀ ℕ) (b : σ →₀ ℕ) :
    Finsupp.weight w (a.sumElim b) =
      Finsupp.weight (w ∘ Sum.inl) a + Finsupp.weight (w ∘ Sum.inr) b := by
  rw [Finsupp.sumElim_eq_add, map_add, WeightedRename.GradedHilbert.naturalWeight_mapDomain, WeightedRename.GradedHilbert.naturalWeight_mapDomain]

theorem iterated_linearPart_homogeneous
    {p : MvPolynomial (ι ⊕ σ) K} {D d : ℕ}
    (hp : p.IsWeightedHomogeneous (Sum.elim (fun _ : ι => D) (fun _ : σ => 1)) d)
    (i : ι) :
    (Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart (sumAlgEquiv K ι σ p) i).IsHomogeneous (d - D) := by
  intro a ha
  change AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff (sumAlgEquiv K ι σ p) (Finsupp.single i 1)) a ≠ 0 at ha
  rw [coeff_coeff_sumAlgEquiv] at ha
  have hd := hp ha
  rw [naturalWeight_sumElim, Finsupp.weight_single] at hd
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, one_smul] at hd
  change Finsupp.weight (fun _ : σ => 1) a = d - D
  omega

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IteratedPolynomialCoefficients.GradedHilbert
