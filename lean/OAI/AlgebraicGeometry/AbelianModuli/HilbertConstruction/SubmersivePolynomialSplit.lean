import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Logic.Equiv.Set

/-! # Submersive Polynomial Split -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersivePolynomialSplit

noncomputable section

/-! Split the variables selected by an injective Jacobian index from the remaining coefficient variables. -/

universe u v w

variable {ι : Type v} {σ : Type w}

abbrev UnselectedVariables (m : σ → ι) := {i : ι // i ∉ Set.range m}

def injectionSumComplementEquiv (m : σ → ι) (hm : Function.Injective m) :
    σ ⊕ UnselectedVariables m ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective m hm) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun i => i ∈ Set.range m))

@[simp]
theorem injectionSumComplementEquiv_inl (m : σ → ι) (hm : Function.Injective m) (j : σ) :
    injectionSumComplementEquiv m hm (.inl j) = m j := rfl

@[simp]
theorem injectionSumComplementEquiv_inr (m : σ → ι) (hm : Function.Injective m)
    (i : UnselectedVariables m) : injectionSumComplementEquiv m hm (.inr i) = i.val := rfl

@[simp]
theorem injectionSumComplementEquiv_symm_selected (m : σ → ι) (hm : Function.Injective m) (j : σ) :
    (injectionSumComplementEquiv m hm).symm (m j) = .inl j := by
  apply (injectionSumComplementEquiv m hm).injective
  rw [Equiv.apply_symm_apply, injectionSumComplementEquiv_inl]

@[simp]
theorem injectionSumComplementEquiv_symm_unselected (m : σ → ι) (hm : Function.Injective m)
    (i : UnselectedVariables m) : (injectionSumComplementEquiv m hm).symm i.val = .inr i := by
  apply (injectionSumComplementEquiv m hm).injective
  rw [Equiv.apply_symm_apply, injectionSumComplementEquiv_inr]

def submersivePolynomialSplit (R : Type u) [CommRing R] (m : σ → ι) (hm : Function.Injective m) :
    MvPolynomial ι R ≃ₐ[R] MvPolynomial σ (MvPolynomial (UnselectedVariables m) R) :=
  (MvPolynomial.renameEquiv R (injectionSumComplementEquiv m hm).symm).trans
    (MvPolynomial.sumAlgEquiv R σ (UnselectedVariables m))

@[simp]
theorem submersivePolynomialSplit_selected (R : Type u) [CommRing R]
    (m : σ → ι) (hm : Function.Injective m) (j : σ) :
    submersivePolynomialSplit R m hm (MvPolynomial.X (m j)) = MvPolynomial.X j := by
  simp [submersivePolynomialSplit]

@[simp]
theorem submersivePolynomialSplit_unselected (R : Type u) [CommRing R]
    (m : σ → ι) (hm : Function.Injective m) (i : UnselectedVariables m) :
    submersivePolynomialSplit R m hm (MvPolynomial.X i.val) = MvPolynomial.C (MvPolynomial.X i) := by
  simp [submersivePolynomialSplit]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubmersivePolynomialSplit
