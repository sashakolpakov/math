import Mathlib

/-! # Laurent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Laurent.Construction

noncomputable section

/-! Laurent-polynomial bounds used to rule out algebraic cocharacters in
compact real matrix groups. -/

open scoped Classical LaurentPolynomial
open Filter _root_.Polynomial

theorem laurent_numerator_degree_le
    (f : LaurentPolynomial ℝ) (P : ℝ[X]) (n : ℕ)
    (hP : P.toLaurent = f * LaurentPolynomial.T n)
    (hbound : ∃ B : ℝ, ∀ t : ℝˣ,
      |LaurentPolynomial.eval₂ (RingHom.id ℝ) t f| ≤ B) :
    P.natDegree ≤ n := by
  obtain ⟨B, hB⟩ := hbound
  have hb : IsBoundedUnder (· ≤ ·) atTop
      (fun x : ℝ => |P.eval x / (X ^ n : ℝ[X]).eval x|) := by
    apply isBoundedUnder_of_eventually_le (a := B)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    let t : ℝˣ := Units.mk0 x hx.ne'
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℝ) t) hP
    simp only [LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id,
      map_mul, LaurentPolynomial.eval₂_T_n] at he
    change P.eval x = LaurentPolynomial.eval₂ (RingHom.id ℝ) t f * x ^ n at he
    rw [Polynomial.eval_pow, Polynomial.eval_X, he]
    change |LaurentPolynomial.eval₂ (RingHom.id ℝ) t f * x ^ n / x ^ n| ≤ B
    rw [mul_div_cancel_right₀ _ (pow_ne_zero n hx.ne')]
    exact hB t
  apply Polynomial.natDegree_le_of_degree_le
  apply le_of_not_gt
  intro hdeg
  have hlim := P.abs_div_tendsto_atTop_atTop_of_degree_gt (X ^ n)
    (by simpa only [Polynomial.degree_X_pow] using hdeg)
    (pow_ne_zero n Polynomial.X_ne_zero)
  exact (not_isBoundedUnder_of_tendsto_atTop hlim) hb

theorem laurent_positive_coeff_eq_zero (f : LaurentPolynomial ℝ)
    (hbound : ∃ B : ℝ, ∀ t : ℝˣ,
      |LaurentPolynomial.eval₂ (RingHom.id ℝ) t f| ≤ B)
    (z : ℤ) (hz : 0 < z) : f.coeff z = 0 := by
  obtain ⟨n, P, hP⟩ := f.exists_T_pow
  have hn := laurent_numerator_degree_le f P n hP hbound
  by_contra hne
  have hmem : z ∈ f.coeff.support := Finsupp.mem_support_iff.mpr hne
  have hshift : z + n ∈ (f * LaurentPolynomial.T n).coeff.support := by
    rw [LaurentPolynomial.T,
      AddMonoidAlgebra.support_coeff_mul_single f 1 (fun y => by simp)]
    exact Finset.mem_map.mpr ⟨z, hmem, rfl⟩
  rw [← hP, LaurentPolynomial.support_coeff_toLaurent] at hshift
  obtain ⟨m, hm, he⟩ := Finset.mem_map.mp hshift
  have hmn := (Polynomial.le_natDegree_of_mem_supp m hm).trans hn
  have hmz : (m : ℤ) = z + n := he
  omega

theorem laurent_eval_invert {R S : Type*} [CommSemiring R] [CommSemiring S]
    (ι : R →+* S) (t : Sˣ) (f : LaurentPolynomial R) :
    LaurentPolynomial.eval₂ ι t (LaurentPolynomial.invert f) =
      LaurentPolynomial.eval₂ ι t⁻¹ f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simpa only [map_add] using congrArg₂ (· + ·) hf hg
  | C_mul_T n a =>
    simp only [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
      LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, zpow_neg, inv_zpow]

/-- A Laurent polynomial bounded on every nonzero real argument is constant. -/
theorem bounded_laurent_eq_constant (f : LaurentPolynomial ℝ)
    (hbound : ∃ B : ℝ, ∀ t : ℝˣ,
      |LaurentPolynomial.eval₂ (RingHom.id ℝ) t f| ≤ B) :
    f = LaurentPolynomial.C (f.coeff 0) := by
  have hi : ∃ B : ℝ, ∀ t : ℝˣ,
      |LaurentPolynomial.eval₂ (RingHom.id ℝ) t (LaurentPolynomial.invert f)| ≤ B := by
    obtain ⟨B, hB⟩ := hbound
    exact ⟨B, fun t => by simpa only [laurent_eval_invert] using hB t⁻¹⟩
  apply LaurentPolynomial.ext
  intro z
  by_cases hz : z = 0
  · subst z
    simp
  rw [LaurentPolynomial.C_apply, ite_eq_right hz]
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have h := laurent_positive_coeff_eq_zero (LaurentPolynomial.invert f) hi (-z)
      (by omega)
    simpa only [LaurentPolynomial.invert_apply, neg_neg] using h
  · exact laurent_positive_coeff_eq_zero f hbound z hpos

theorem laurent_map_C {R S : Type*} [CommSemiring R] [CommSemiring S]
    (ι : R →+* S) (a : R) :
    AddMonoidAlgebra.mapRingHom ℤ ι (LaurentPolynomial.C a) =
      LaurentPolynomial.C (ι a) := by
  apply LaurentPolynomial.ext
  intro n
  simp only [AddMonoidAlgebra.coeff_mapRingHom, LaurentPolynomial.C_apply]
  split_ifs <;> simp

theorem laurent_map_T {R S : Type*} [CommSemiring R] [CommSemiring S]
    (ι : R →+* S) (n : ℤ) :
    AddMonoidAlgebra.mapRingHom ℤ ι (LaurentPolynomial.T n) =
      LaurentPolynomial.T n := by
  simp only [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]

theorem laurent_eval_map {R S K : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring K]
    (ι : R →+* S) (κ : S →+* K) (t : Kˣ) (f : LaurentPolynomial R) :
    LaurentPolynomial.eval₂ κ t (AddMonoidAlgebra.mapRingHom ℤ ι f) =
      LaurentPolynomial.eval₂ (κ.comp ι) t f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simpa only [map_add] using congrArg₂ (· + ·) hf hg
  | C_mul_T n a =>
    simp only [map_mul, laurent_map_C, laurent_map_T,
      LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, RingHom.comp_apply]

/-- A real embedding detects every nonconstant Laurent coefficient. -/
theorem laurent_constant_of_real_bound {k : Type*} [Field k]
    (v : k →+* ℝ) (f : LaurentPolynomial k)
    (hbound : ∃ B : ℝ, ∀ t : ℝˣ, |LaurentPolynomial.eval₂ v t f| ≤ B) :
    f = LaurentPolynomial.C (f.coeff 0) := by
  have hb : ∃ B : ℝ, ∀ t : ℝˣ,
      |LaurentPolynomial.eval₂ (RingHom.id ℝ) t
        (AddMonoidAlgebra.mapRingHom ℤ v f)| ≤ B := by
    simpa only [laurent_eval_map, RingHom.id_comp] using hbound
  have he := bounded_laurent_eq_constant (AddMonoidAlgebra.mapRingHom ℤ v f) hb
  apply LaurentPolynomial.ext
  intro z
  apply v.injective
  have hc := congrArg (fun q : LaurentPolynomial ℝ => q.coeff z) he
  simp only [AddMonoidAlgebra.coeff_mapRingHom, LaurentPolynomial.C_apply] at hc ⊢
  split_ifs at hc ⊢ <;> simpa only [map_zero] using hc

/-- Substitute (T,T⁻¹) in a polynomial in two coordinates. -/
def laurentOfPair {k : Type*} [CommSemiring k] (p : MvPolynomial (Fin 2) k) :
    LaurentPolynomial k :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C
    (fun i : Fin 2 => if i = 0 then LaurentPolynomial.T 1 else LaurentPolynomial.T (-1)) p

theorem eval_laurentOfPair {k K : Type*} [CommSemiring k] [CommSemiring K]
    (ι : k →+* K) (t : Kˣ) (p : MvPolynomial (Fin 2) k) :
    LaurentPolynomial.eval₂ ι t (laurentOfPair p) =
      MvPolynomial.eval₂Hom ι
        (fun i : Fin 2 => if i = 0 then (t : K) else ((t⁻¹ : Kˣ) : K)) p := by
  have hh :
      (LaurentPolynomial.eval₂ ι t).comp
        (MvPolynomial.eval₂Hom LaurentPolynomial.C
          (fun i : Fin 2 => if i = 0 then LaurentPolynomial.T 1 else LaurentPolynomial.T (-1))) =
      MvPolynomial.eval₂Hom ι
        (fun i : Fin 2 => if i = 0 then (t : K) else ((t⁻¹ : Kˣ) : K)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [LaurentPolynomial.eval₂_C]
    · intro i
      by_cases hi : i = 0 <;> simp [hi, LaurentPolynomial.eval₂_T]
  exact DFunLike.congr_fun hh p

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Laurent.Construction
