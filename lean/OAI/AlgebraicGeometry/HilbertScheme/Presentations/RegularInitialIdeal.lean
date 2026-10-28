import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedOrder
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.MonomialBound

/-! # Regular Initial Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularInitialIdeal.GradedHilbert

noncomputable section

/-!
A variable that is regular modulo a homogeneous ideal stays regular
modulo its initial ideal for the weighted order constructed above.
This gives saturated initial ideals and bounded homogeneous generators.
-/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

def VariableRegular (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (i : Fin (n + 1)) : Prop :=
  ∀ f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n, X i * f ∈ I → f ∈ I

theorem VariableRegular.pow {I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)} {i : Fin (n + 1)}
    (hI : VariableRegular I i) (m : ℕ) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    X i ^ m * f ∈ I → f ∈ I := by
  induction m with
  | zero => simpa only [pow_zero, one_mul] using (id : f ∈ I → f ∈ I)
  | succ m ih =>
      intro hf
      apply ih
      apply hI
      simpa only [pow_succ', mul_assoc] using hf

theorem VariableRegular.isSaturated {I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)} {i : Fin (n + 1)}
    (hI : VariableRegular I i) : Hilbert.Polynomial.GradedHilbert.IsSaturated I := by
  intro f _ _ hf
  obtain ⟨m, hm⟩ := hf
  exact hI.pow m f (hm (X i ^ m) (isHomogeneous_X_pow i m))

theorem variable_dvd_of_leading_exponent_pos (i : Fin (n + 1))
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} {d : ℕ} (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (hi : 0 < (WeightedOrder.GradedHilbert.variableLastOrder i).degree f i) : X i ∣ f := by
  classical
  apply X_dvd_iff_modMonomial_eq_zero.mpr
  apply MvPolynomial.ext
  intro a
  rw [AddMonoidAlgebra.coeff_zero]
  by_cases ha : Finsupp.single i 1 ≤ a
  · exact coeff_modMonomial_of_le f ha
  · rw [coeff_modMonomial_of_not_le f ha]
    by_contra hcoeff
    have hle := WeightedOrder.GradedHilbert.leading_variable_exponent_le i hf hf0 (mem_support_iff.mpr hcoeff)
    exact ha (Finsupp.single_le_iff.mpr (hi.trans_le hle))

theorem initial_monomial_cancel_variable (i : Fin (n + 1))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : VariableRegular I.toIdeal i)
    (a : Fin (n + 1) →₀ ℕ)
    (ha : monomial (Finsupp.single i 1 + a) (1 : K) ∈
      InitialIdeal.GradedHilbert.initialIdeal (WeightedOrder.GradedHilbert.variableLastOrder i) I.toIdeal) :
    monomial a (1 : K) ∈ InitialIdeal.GradedHilbert.initialIdeal (WeightedOrder.GradedHilbert.variableLastOrder i) I.toIdeal := by
  classical
  let m := WeightedOrder.GradedHilbert.variableLastOrder i
  obtain ⟨f, hf, hf0, hhom, hfa⟩ := GroebnerGenerators.GradedHilbert.lift_initial_monomial m I _ ha
  by_cases hfi : m.degree f i = 0
  · apply (InitialIdeal.GradedHilbert.monomial_mem_initialIdeal_iff m I.toIdeal a).mpr
    refine ⟨f, hf, hf0, fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      simp only [hfi, zero_le]
    · simpa only [Finsupp.add_apply, Finsupp.single_apply, ite_eq_right (Ne.symm hji), zero_add] using hfa j
  · obtain ⟨g, hfg⟩ := variable_dvd_of_leading_exponent_pos i hhom hf0 (Nat.pos_of_ne_zero hfi)
    have hg : g ∈ I.toIdeal := hI g (hfg ▸ hf)
    have hg0 : g ≠ 0 := by
      intro hg0
      rw [hg0, mul_zero] at hfg
      exact hf0 hfg
    have hdeg : m.degree f = Finsupp.single i 1 + m.degree g := by
      rw [hfg, m.degree_mul (X_ne_zero i) hg0, m.degree_X]
    rw [hdeg] at hfa
    exact (InitialIdeal.GradedHilbert.monomial_mem_initialIdeal_iff m I.toIdeal a).mpr
      ⟨g, hg, hg0, fun j => Nat.le_of_add_le_add_left (hfa j)⟩

theorem initialIdeal_variableRegular (i : Fin (n + 1))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : VariableRegular I.toIdeal i) :
    VariableRegular (InitialIdeal.GradedHilbert.initialIdeal (WeightedOrder.GradedHilbert.variableLastOrder i) I.toIdeal) i := by
  intro f hf
  have hMon := InitialIdeal.GradedHilbert.initialIdeal_isMonomial (WeightedOrder.GradedHilbert.variableLastOrder i) I.toIdeal
  apply (hMon.mem_iff_support f).mpr
  intro a ha
  apply initial_monomial_cancel_variable i I hI a
  apply (hMon.mem_iff_support (X i * f)).mp hf (Finsupp.single i 1 + a)
  rw [mem_support_iff, coeff_X_mul]
  exact mem_support_iff.mp ha

theorem initialIdeal_isSaturated (i : Fin (n + 1))
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : VariableRegular I.toIdeal i) :
    Hilbert.Polynomial.GradedHilbert.IsSaturated (InitialIdeal.GradedHilbert.initialIdeal (WeightedOrder.GradedHilbert.variableLastOrder i) I.toIdeal) :=
  (initialIdeal_variableRegular i I hI).isSaturated

/-- A bound depending only on the number of variables and Hilbert
polynomial for ideals with a regular coordinate variable. -/
theorem exists_uniform_homogeneous_degree_bound_of_variableRegular
    (n : ℕ) (P : Polynomial ℚ) :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
      (i : Fin (n + 1)), VariableRegular I.toIdeal i → Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P →
      ∃ B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n), I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ∧
        ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ N, b.IsHomogeneous d := by
  obtain ⟨N, hN⟩ := Uniform.MonomialBound.GradedHilbert.exists_field_independent_monomial_degree_bound.{u} n P
  refine ⟨N, fun K _ I i hI hP => ?_⟩
  let m := WeightedOrder.GradedHilbert.variableLastOrder i
  let J := InitialIdeal.GradedHilbert.initialHomogeneousIdeal m I.toIdeal
  have hPJ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P :=
    (InitialIdeal.GradedHilbert.hasHilbertPolynomial_initialIdeal_iff m I P).mpr hP
  obtain ⟨G, hG, hdeg⟩ := hN K J (InitialIdeal.GradedHilbert.initialIdeal_isMonomial m I.toIdeal)
    (initialIdeal_isSaturated i I hI) hPJ
  exact GroebnerGenerators.GradedHilbert.homogeneous_generators_of_initial_generators m I G N hG hdeg

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.RegularInitialIdeal.GradedHilbert
