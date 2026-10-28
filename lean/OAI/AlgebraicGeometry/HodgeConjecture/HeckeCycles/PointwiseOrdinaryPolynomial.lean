import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial

/-! # Pointwise Ordinary Polynomial -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointwiseOrdinaryPolynomial.CM.Ordinary

/-! The literal ordinary-neighbor identities make the Hecke polynomial
annihilate every same-component Albanese difference, before detection. -/

open OAI.RepresentationTheory.Hecke.CubicRelation OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Polynomial.CM

theorem polynomial_annihilates_differences
    (q : ℕ) {R A O J : Type*} [Ring R] [AddCommGroup A]
    (act : R →+* AddMonoid.End A) (component : O → J) (a : O → A)
    (Φ : R) (H : Fin 3 → R) (X Z : O → O) (Y : O → Multiset O)
    (hXcomponent : ∀ x, component (X x) = component x)
    (hFrobenius : ∀ x, act Φ (a x) = a (X x))
    (hH : ∀ (i : Fin 3) (x y : O), component x = component y →
      act (H i) (a x - a y) =
        ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X Z Y i x).map a).sum -
          ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q X Z Y i y).map a).sum)
    (x y : O) (hxy : component x = component y) :
    act (Ordinary.Polynomial.CM.heckePolynomialValue q Φ H) (a x - a y) = 0 := by
  have hT1 (x y : O) (hxy : component x = component y) :
      act (H 0) (a x - a y) = a (X x) - a (X y) +
        q • (((Y x).map a).sum - ((Y y).map a).sum) := by
    rw [hH 0 x y hxy]
    simp [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors, Ordinary.Polynomial.CM.sum_map_nsmul, smul_sub]
    abel
  have hT2 (x y : O) (hxy : component x = component y) :
      act (H 1) (a x - a y) =
        ((Y (X x)).map a).sum - ((Y (X y)).map a).sum +
          q ^ 2 • (a (Z x) - a (Z y)) := by
    rw [hH 1 x y hxy]
    simp [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors, Ordinary.Polynomial.CM.sum_map_nsmul, smul_sub]
    abel
  have hT3 (x y : O) (hxy : component x = component y) :
      act (H 2) (a x - a y) = a (Z (X x)) - a (Z (X y)) := by
    rw [hH 2 x y hxy]
    simp [RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors]
  change act (Φ ^ 3 - H 0 * Φ ^ 2 + q • (H 1 * Φ) - q ^ 3 • H 2) (a x - a y) = 0
  have hxy1 : component (X x) = component (X y) := by
    simpa only [hXcomponent] using hxy
  have hxy2 : component (X (X x)) = component (X (X y)) := by
    simpa only [hXcomponent] using hxy
  have hmul (f g : R) (b : A) : act (f * g) b = act f (act g b) := by
    rw [map_mul]
    rfl
  have hsub (f g : R) (b : A) : act (f - g) b = act f b - act g b := by
    rw [map_sub]
    rfl
  have hadd (f g : R) (b : A) : act (f + g) b = act f b + act g b := by
    rw [map_add]
    rfl
  have hsmul (n : ℕ) (f : R) (b : A) : act (n • f) b = n • act f b := by
    rw [map_nsmul]
    rfl
  have hpow (n : ℕ) (z : O) :
      act (Φ ^ n) (a z) = a (X^[n] z) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', hmul, ih, hFrobenius, Function.iterate_succ_apply']
  have hpow_sub (n : ℕ) (z w : O) :
      act (Φ ^ n) (a z - a w) = a (X^[n] z) - a (X^[n] w) := by
    rw [map_sub, hpow, hpow]
  have hφ (z w : O) : act Φ (a z - a w) = a (X z) - a (X w) := by
    rw [map_sub, hFrobenius, hFrobenius]
  simp only [hsub, hadd, hsmul]
  rw [hmul (H 0), hmul (H 1), hpow_sub, hpow_sub, hφ]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [hT1 _ _ hxy2, hT2 _ _ hxy1, hT3 _ _ hxy]
  simp only [smul_add, smul_smul, ← pow_succ']
  abel

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointwiseOrdinaryPolynomial.CM.Ordinary
