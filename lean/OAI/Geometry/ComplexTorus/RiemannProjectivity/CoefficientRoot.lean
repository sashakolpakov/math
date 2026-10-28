import OAI.Geometry.ComplexTorus.RiemannProjectivity.BranchCoefficientsAt
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-! # Coefficient Root -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot.Constructions.CoefficientGrowth

/-!
# RiemannProjectivity: growth bounds for projection coefficients

The proper-cone norm estimate bounds every coordinate on a fiber. The
product polynomial of a finite fiber therefore has polynomially bounded
coefficients, with an explicit constant and degree. Repeated coordinate
values remain separate factors, as required for symmetric coefficients.
-/

open Set _root_.Polynomial
open scoped BigOperators

theorem norm_coeff_prod_X_sub_C_le {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (R : ℝ) (ha : ∀ i, ‖a i‖ ≤ R) (j : ℕ) :
    ‖(∏ i, (Polynomial.X - Polynomial.C (a i))).coeff j‖ ≤
      (Fintype.card ι).choose j * (max 1 R) ^ Fintype.card ι := by
  classical
  have hm : ∀ s : Finset ι,
      (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).mahlerMeasure =
        ∏ i ∈ s, max 1 ‖a i‖ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.prod_insert hi, Polynomial.mahlerMeasure_mul, ih,
        Polynomial.mahlerMeasure_X_sub_C]
  have hprod : (∏ i, max 1 ‖a i‖) ≤ (max 1 R) ^ Fintype.card ι := by
    calc
      _ ≤ ∏ _ : ι, max 1 R := Finset.prod_le_prod₀
        (fun _ _ => le_trans zero_le_one (le_max_left _ _))
        (fun i _ => max_le_max_left 1 (ha i))
      _ = _ := by simp
  calc
    _ ≤ (∏ i, (Polynomial.X - Polynomial.C (a i))).natDegree.choose j *
        (∏ i, (Polynomial.X - Polynomial.C (a i))).mahlerMeasure :=
      Polynomial.norm_coeff_le_choose_mul_mahlerMeasure _ _
    _ = (Fintype.card ι).choose j * ∏ i, max 1 ‖a i‖ := by simp only [hm,
        Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W]

/-- The linear bound on a fiber gives the polynomial-growth hypothesis
needed for extension of each symmetric coefficient. -/
theorem coefficient_growth_from_fiber_bound {m : ℕ} (b : Fin m → W → V)
    (l : V →L[ℂ] ℂ) (C : ℝ) {U : Set W}
    (hb : ∀ z ∈ U, ∀ i, ‖b i z‖ ≤ C * ‖z‖) (j : ℕ) :
    ∀ z ∈ U,
      ‖(∏ i, (Polynomial.X - Polynomial.C (l (b i z)))).coeff j‖ ≤
        ((m.choose j : ℝ) * (max 1 (‖l‖ * C)) ^ m) * (max 1 ‖z‖) ^ m := by
  intro z hz
  have ha : ∀ i, ‖l (b i z)‖ ≤ ‖l‖ * C * ‖z‖ := fun i =>
    (l.le_opNorm _).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb z hz i) (norm_nonneg l))
  have hmax : max 1 (‖l‖ * C * ‖z‖) ≤ max 1 (‖l‖ * C) * max 1 ‖z‖ := by
    apply max_le
    · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
    · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (norm_nonneg z)
        (le_trans zero_le_one (le_max_left _ _))
  calc
    _ ≤ (m.choose j : ℝ) * (max 1 (‖l‖ * C * ‖z‖)) ^ m := by
      simpa only [Fintype.card_fin] using norm_coeff_prod_X_sub_C_le
        (fun i => l (b i z)) (‖l‖ * C * ‖z‖) ha j
    _ ≤ (m.choose j : ℝ) * (max 1 (‖l‖ * C) * max 1 ‖z‖) ^ m := by gcongr
    _ = _ := by rw [mul_pow, mul_assoc]

variable [NormedSpace ℂ W] {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Combine genuine local inverse branches with a uniform fiber bound.
The same local polynomial has both holomorphic coefficients and the
quantitative growth estimate. -/
theorem local_bounded_fiber_polynomial (a : X → V) {f : X → W} (hf : IsProperMap f)
    (C : ℝ) (hbound : ∀ x, ‖a x‖ ≤ C * ‖f x‖)
    {y : W} (hy : y ∈ BranchCoefficientsAt.Constructions.BranchCoefficients.holomorphicRegularValues a f)
    (l : V →L[ℂ] ℂ) :
    ∃ (m : ℕ) (U : Set W) (P : W → Polynomial ℂ), IsOpen U ∧ y ∈ U ∧
      (∀ j, DifferentiableOn ℂ (fun z => (P z).coeff j) U) ∧
      (∀ z ∈ U, ∀ j, ‖(P z).coeff j‖ ≤
        ((m.choose j : ℝ) * (max 1 (‖l‖ * C)) ^ m) * (max 1 ‖z‖) ^ m) ∧
      ∀ z ∈ U, (P z).Monic ∧
        ∀ c, (P z).eval c = 0 ↔ ∃ x, f x = z ∧ l (a x) = c := by
  obtain ⟨m, U, b, hU, hyU, hb, hbij⟩ := BranchCoefficientsAt.Constructions.BranchCoefficients.finite_holomorphic_branches a hf hy
  have hp := BranchCoefficientsAt.Constructions.BranchCoefficients.polynomial_of_holomorphic_branches a f b hb
    (fun z hz => (hbij z hz).2) l
  refine ⟨m, U, _, hU, hyU, hp.1, ?_, hp.2⟩
  intro z hz j
  apply coefficient_growth_from_fiber_bound (fun i w => a (b i w)) l C ?_ j z hz
  intro w hw i
  have hfw : f (b i w) = w := ((hbij w hw).2 _).mpr ⟨i, rfl⟩
  simpa only [hfw] using hbound (b i w)

end Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot.Constructions.CoefficientGrowth

namespace Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot.Constructions.RootCoefficientBound

/-! # RiemannProjectivity: coefficient bounds from bounded roots, including multiplicities -/

open _root_.Polynomial
open scoped BigOperators

theorem prod_max_norm_le (s : Multiset ℂ) (R : ℝ) (h : ∀ z ∈ s, ‖z‖ ≤ R) :
    (s.map (fun z => max 1 ‖z‖)).prod ≤ (max 1 R) ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    have hz : ‖z‖ ≤ R := h z (Multiset.mem_cons_self _ _)
    have hs : ∀ w ∈ s, ‖w‖ ≤ R := fun w hw => h w (Multiset.mem_cons_of_mem hw)
    have hn : 0 ≤ (s.map (fun w => max 1 ‖w‖)).prod := by
      apply Multiset.prod_nonneg
      intro a ha
      obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp ha
      exact zero_le_one.trans (le_max_left _ _)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc
      _ ≤ max 1 R * (max 1 R) ^ s.card :=
        mul_le_mul (max_le_max_left 1 hz) (ih hs) hn (zero_le_one.trans (le_max_left _ _))
      _ = _ := mul_comm _ _

theorem norm_coeff_le {p : Polynomial ℂ} (hp : p.Monic) {R : ℝ}
    (hroot : ∀ z : ℂ, p.eval z = 0 → ‖z‖ ≤ R) (j : ℕ) :
    ‖p.coeff j‖ ≤ (p.natDegree.choose j : ℝ) * (max 1 R) ^ p.natDegree := by
  have hroots : ∀ z ∈ p.roots, ‖z‖ ≤ R := fun z hz => hroot z ((mem_roots hp.ne_zero).mp hz)
  have hb := prod_max_norm_le p.roots R hroots
  rw [← (IsAlgClosed.splits p).natDegree_eq_card_roots] at hb
  have hm : p.mahlerMeasure ≤ (max 1 R) ^ p.natDegree := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hp.leadingCoeff, norm_one, one_mul]
    exact hb
  exact (norm_coeff_le_choose_mul_mahlerMeasure j p).trans
    (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _))

end Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot.Constructions.RootCoefficientBound

namespace Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot.Constructions.MonicFamily

/-! # RiemannProjectivity: reconstructing a monic polynomial from its lower coefficients -/

open _root_.Polynomial
open scoped BigOperators

def ofCoefficients (k : ℕ) (a : ℕ → ℂ) : ℂ[X] :=
  X ^ k + ∑ j ∈ Finset.range k, monomial j (a j)

theorem coeff_ofCoefficients (k j : ℕ) (a : ℕ → ℂ) :
    (ofCoefficients k a).coeff j = (if j = k then 1 else 0) +
      (if j < k then a j else 0) := by
  classical
  simp [ofCoefficients, coeff_monomial, coeff_X_pow, eq_comm]

theorem monic_ofCoefficients (k : ℕ) (a : ℕ → ℂ) :
    (ofCoefficients k a).Monic ∧ (ofCoefficients k a).natDegree = k := by
  have hd : (ofCoefficients k a).natDegree ≤ k := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp [coeff_ofCoefficients, ne_of_gt hj, not_lt_of_ge (Nat.le_of_lt hj)]
  have hc : (ofCoefficients k a).coeff k = 1 := by simp [coeff_ofCoefficients]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one k hd hc,
    le_antisymm hd (le_natDegree_of_ne_zero (by rw [hc]; exact one_ne_zero))⟩

theorem ofCoefficients_eq {p : ℂ[X]} (hp : p.Monic) {k : ℕ} (hd : p.natDegree = k)
    {a : ℕ → ℂ} (ha : ∀ j < k, a j = p.coeff j) : ofCoefficients k a = p := by
  ext j
  rw [coeff_ofCoefficients]
  by_cases hj : j < k
  · simp [hj, ne_of_lt hj, ha j hj]
  · by_cases he : j = k
    · subst j
      simp [← hd, hp.coeff_natDegree]
    · have hk : p.natDegree < j := by omega
      simp [he, hj, coeff_eq_zero_of_natDegree_lt hk]

end Geometry.ComplexTorus.RiemannProjectivity.CoefficientRoot.Constructions.MonicFamily

end

end OAI
