import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentMonomialBasis
import Mathlib.Basic.Complex.Basic

/-! # Monomial Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.MonomialEvaluation.Dolbeault

noncomputable section

/-! Evaluation of the original localized Laurent monomials wherever their denominators are nonzero. -/

open scoped BigOperators

variable {ι : Type} [Fintype ι]

def allowedLaurentMonomialEvaluation (m : ι →₀ ℕ) (x : ι → ℂ)
    (hx : ∀ i, m i ≠ 0 → x i ≠ 0) :
    Multiplicative (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m) →* ℂ where
  toFun e := ∏ i, x i ^ e.toAdd.val i
  map_one' := by simp
  map_mul' e f := by
    change (∏ i, x i ^ (e.toAdd.val i + f.toAdd.val i)) =
      (∏ i, x i ^ e.toAdd.val i) * ∏ i, x i ^ f.toAdd.val i
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    apply zpow_add'
    by_cases hi : x i ≠ 0
    · exact Or.inl hi
    · have hm : m i = 0 := by by_contra hm; exact hi (hx i hm)
      have he : 0 ≤ e.toAdd.val i := le_of_not_gt (fun h => e.toAdd.property i h hm)
      have hf : 0 ≤ f.toAdd.val i := le_of_not_gt (fun h => f.toAdd.property i h hm)
      right
      omega

def allowedLaurentEvaluation (m : ι →₀ ℕ) (x : ι → ℂ)
    (hx : ∀ i, m i ≠ 0 → x i ≠ 0) :
    AddMonoidAlgebra ℂ (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m) →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m)
    (allowedLaurentMonomialEvaluation m x hx)

theorem allowedLaurentEvaluation_single (m : ι →₀ ℕ) (x : ι → ℂ)
    (hx : ∀ i, m i ≠ 0 → x i ≠ 0)
    (e : SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m) (c : ℂ) :
    allowedLaurentEvaluation m x hx (AddMonoidAlgebra.single e c) = c * ∏ i, x i ^ e.val i :=
  AddMonoidAlgebra.lift_single (allowedLaurentMonomialEvaluation m x hx) e c

theorem allowedLaurentEvaluation_polynomial (m : ι →₀ ℕ) (x : ι → ℂ)
    (hx : ∀ i, m i ≠ 0 → x i ≠ 0) (P : MvPolynomial ι ℂ) :
    allowedLaurentEvaluation m x hx
      (AddMonoidAlgebra.mapDomain (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap m).toAddMonoidHom P) =
        MvPolynomial.eval x P := by
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    change allowedLaurentEvaluation m x hx
      (AddMonoidAlgebra.mapDomain (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap m).toAddMonoidHom
        (AddMonoidAlgebra.single e c)) = _
    rw [AddMonoidAlgebra.mapDomain_single, allowedLaurentEvaluation_single, MvPolynomial.eval_monomial]
    rw [Finsupp.prod_pow]
    change c * (∏ i, x i ^ (e i : ℤ)) = c * ∏ i, x i ^ e i
    simp only [zpow_natCast]
  | add P Q hP hQ =>
    rw [AddMonoidAlgebra.mapDomain_add, map_add, MvPolynomial.eval_add, hP, hQ]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.MonomialEvaluation.Dolbeault
