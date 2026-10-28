import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContraction
import OAI.Analysis.HodgeTheory.Decomposition.InfinitesimalTypeEigen

/-! # Antiholomorphic Contraction Vanishing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionVanishing.Dolbeault

noncomputable section

/-! A positive antiholomorphic pure covector vanishes when all its
antiholomorphic contractions vanish. The proof compares actual infinitesimal
complex rotation with the differentiated scalar character. -/

open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
theorem contraction_zero_update_first_I (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (ha : ∀ v : E, AntiholomorphicContraction.Dolbeault.antiContraction n v a = 0) (w : Fin (n + 1) → E) :
    a (Function.update w 0 (Complex.I • w 0)) = Complex.I * a w := by
  have h := congrArg (fun b : Analysis.DifferentialForms.Manifold.Basic.FormValue E n => b (Fin.tail w)) (ha (w 0))
  rw [AntiholomorphicContraction.Dolbeault.antiContraction_apply] at h
  have hcons : (Fin.cons (Complex.I • w 0) (Fin.tail w) : Fin (n + 1) → E) =
      Function.update w 0 (Complex.I • w 0) := by
    funext i
    exact Fin.cases (by simp) (fun j => by simp [Fin.tail]) i
  rw [Fin.cons_self_tail, hcons] at h
  change (1 / 2 : ℂ) * (a w + Complex.I * a (Function.update w 0 (Complex.I • w 0))) = 0 at h
  have hz := (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hh := congrArg (fun c : ℂ => (-Complex.I) * c) hz
  simp only [mul_add, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul, mul_zero] at hh
  simpa only [neg_mul, neg_neg] using eq_neg_of_add_eq_zero_right hh

omit [IsScalarTower ℝ ℂ E] in
theorem contraction_zero_update_I (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (ha : ∀ v : E, AntiholomorphicContraction.Dolbeault.antiContraction n v a = 0) (w : Fin (n + 1) → E) (i : Fin (n + 1)) :
    a (Function.update w i (Complex.I • w i)) = Complex.I * a w := by
  by_cases hi : i = 0
  · subst i
    exact contraction_zero_update_first_I n a ha w
  · have h := contraction_zero_update_first_I n a ha (w ∘ Equiv.swap i 0)
    have he := Function.update_comp_equiv w (Equiv.swap i 0) i (Complex.I • w i)
    simp only [Equiv.symm_swap, Equiv.swap_apply_left] at he
    simp only [Function.comp_apply, Equiv.swap_apply_right] at h
    rw [← he] at h
    have hleft := a.toAlternatingMap.map_swap (Function.update w i (Complex.I • w i)) hi
    have hright := a.toAlternatingMap.map_swap w hi
    change a (Function.update w i (Complex.I • w i) ∘ Equiv.swap i 0) =
      -a (Function.update w i (Complex.I • w i)) at hleft
    change a (w ∘ Equiv.swap i 0) = -a w at hright
    rw [hleft, hright, mul_neg] at h
    exact neg_injective h

theorem contraction_zero_rotation (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (ha : ∀ v : E, AntiholomorphicContraction.Dolbeault.antiContraction n v a = 0) :
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a =
      (Complex.I * (n + 1 : ℕ)) • a := by
  ext w
  rw [Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction_apply]
  change (∑ i : Fin (n + 1), a (Function.update w i (Complex.I • w i))) =
    (Complex.I * (n + 1 : ℕ)) * a w
  simp only [contraction_zero_update_I n a ha, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem pureCovector_eq_zero_of_antiContractions (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q + 1)) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p (q + 1) a)
    (hz : ∀ v : E, AntiholomorphicContraction.Dolbeault.antiContraction (p + q) v a = 0) : a = 0 := by
  have hrot := contraction_zero_rotation (p + q) a hz
  have hp := Analysis.HodgeTheory.Decomposition.InfinitesimalTypeEigen.Constructions.covectorInfinitesimalRotation_pure p (q + 1) a ha
  have he : (Complex.I * ((p : ℂ) - (q + 1 : ℕ))) • a =
      (Complex.I * (p + q + 1 : ℕ)) • a := hp.symm.trans hrot
  ext w
  have hev := congrArg (fun b : Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q + 1) => b w) he
  change (Complex.I * ((p : ℂ) - (q + 1 : ℕ))) * a w =
    (Complex.I * (p + q + 1 : ℕ)) * a w at hev
  have hmul : (Complex.I * ((p : ℂ) - (q + 1 : ℕ)) -
      Complex.I * (p + q + 1 : ℕ)) * a w = 0 := by
    rw [sub_mul, hev, sub_self]
  apply (mul_eq_zero.mp hmul).resolve_left
  intro hc
  have hn : (p : ℂ) - (q + 1 : ℕ) = (p + q + 1 : ℕ) :=
    mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp hc)
  have hi : (p : ℤ) - (q + 1 : ℕ) = (p + q + 1 : ℕ) := by exact_mod_cast hn
  omega

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionVanishing.Dolbeault
