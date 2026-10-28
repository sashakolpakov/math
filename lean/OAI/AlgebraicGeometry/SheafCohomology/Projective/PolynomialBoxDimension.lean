import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Fintype.Card

/-! # Polynomial Box Dimension -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialBoxDimension.Dimension

noncomputable section

/-! Polynomial spaces with bounded degree in each variable have explicit dimensions. -/

open _root_.MvPolynomial

def boundedExponentEquiv {σ : Type*} [Fintype σ] (n : ℕ) :
    ↥{s : σ →₀ ℕ | ∀ i, s i ≤ n} ≃ (σ → Fin (n + 1)) where
  toFun s i := ⟨s.1 i, Nat.lt_succ_of_le (s.2 i)⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f i).val),
    fun i => Nat.le_of_lt_succ (f i).isLt⟩
  left_inv s := by apply Subtype.ext; ext i; rfl
  right_inv f := by funext i; apply Fin.ext; rfl

theorem finrank_polynomial_restrictDegree
    (K : Type*) [Field K] (σ : Type*) [Fintype σ] (n : ℕ) :
    Module.finrank K (MvPolynomial.restrictDegree σ K n) = (n + 1) ^ Fintype.card σ := by
  classical
  let e := boundedExponentEquiv (σ := σ) n
  let : Fintype ↥{s : σ →₀ ℕ | ∀ i, s i ≤ n} := Fintype.ofEquiv (σ → Fin (n + 1)) e.symm
  change Module.finrank K (MvPolynomial.restrictSupport K {s : σ →₀ ℕ | ∀ i, s i ≤ n}) = _
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K _), Fintype.card_congr e]
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem polynomial_restrictDegree_le_restrictTotalDegree
    (K : Type*) [CommSemiring K] (σ : Type*) [Fintype σ] (n : ℕ) :
    MvPolynomial.restrictDegree σ K n ≤
      MvPolynomial.restrictTotalDegree σ K (Fintype.card σ * n) := by
  classical
  intro p hp
  rw [MvPolynomial.mem_restrictTotalDegree, MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro s hs
  have hbound : ∀ i, s i ≤ n := (MvPolynomial.mem_restrictDegree σ p n).mp hp s hs
  calc
    s.sum (fun _ e => e) = ∑ i : σ, s i := by
      exact Finsupp.sum_fintype _ _ (fun _ => rfl)
    _ ≤ ∑ _i : σ, n := Finset.sum_le_sum (fun i _ => hbound i)
    _ = Fintype.card σ * n := by simp

theorem finrank_polynomial_restrictTotalDegree_le
    (K : Type*) [Field K] (σ : Type*) [Fintype σ] (n : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree σ K n) ≤ (n + 1) ^ Fintype.card σ := by
  rw [← finrank_polynomial_restrictDegree K σ n]
  exact LinearMap.finrank_le_finrank_of_injective
    (Submodule.inclusion_injective (MvPolynomial.restrictTotalDegree_le_restrictDegree σ K n))

theorem finrank_polynomial_restrictTotalDegree_ge
    (K : Type*) [Field K] (σ : Type*) [Fintype σ] (n : ℕ) :
    (n + 1) ^ Fintype.card σ ≤
      Module.finrank K (MvPolynomial.restrictTotalDegree σ K (Fintype.card σ * n)) := by
  rw [← finrank_polynomial_restrictDegree K σ n]
  exact LinearMap.finrank_le_finrank_of_injective
    (Submodule.inclusion_injective (polynomial_restrictDegree_le_restrictTotalDegree K σ n))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialBoxDimension.Dimension
