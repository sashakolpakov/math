import OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalLeibniz

/-! # Total Boundaries -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalBoundaries.CechCup

noncomputable section

/-! Products of closed total cochains are closed, and multiplying a
boundary by a closed cochain gives an explicit boundary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R)))
  (N : SimplicialObject (FormalCoproduct.{u} X.left.Opens))

omit [Algebra ℚ R] in
theorem totalDegreeCast_d_target {a b c : ℕ} (h : b = c) (x : (TotalCup.Cech.total R X N).X a) :
    TotalComponents.CechCup.totalDegreeCast R X N h ((TotalCup.Cech.total R X N).d a b x) = (TotalCup.Cech.total R X N).d a c x := by
  subst c
  rfl

theorem totalDegreeCast_cupInto {p q a b : ℕ} (h : a = b) (hpq : p + q = a)
    (x : (TotalCup.Cech.total R X N).X p) (y : (TotalCup.Cech.total R X N).X q) :
    TotalComponents.CechCup.totalDegreeCast R X N h (TotalComponents.CechCup.cupInto R X N p q a hpq x y) =
      TotalComponents.CechCup.cupInto R X N p q b (hpq.trans h) x y := by
  subst b
  rfl

theorem totalCup_closed (p q : ℕ) (x : (TotalCup.Cech.total R X N).X p) (y : (TotalCup.Cech.total R X N).X q)
    (hx : (TotalCup.Cech.total R X N).d p (p + 1) x = 0) (hy : (TotalCup.Cech.total R X N).d q (q + 1) y = 0) :
    (TotalCup.Cech.total R X N).d (p + q) (p + q + 1) (TotalCup.Cech.totalCup R X N p q x y) = 0 := by
  rw [TotalLeibniz.CechCup.differential_totalCup, hx, hy, map_zero, map_zero]
  simp only [LinearMap.zero_apply, smul_zero, add_zero]

theorem differential_totalCup_right_closed (p q k : ℕ) (hk : (p + 1) + q = k)
    (x : (TotalCup.Cech.total R X N).X p) (y : (TotalCup.Cech.total R X N).X q)
    (hy : (TotalCup.Cech.total R X N).d q (q + 1) y = 0) :
    (TotalCup.Cech.total R X N).d (p + q) k (TotalCup.Cech.totalCup R X N p q x y) =
      TotalComponents.CechCup.cupInto R X N (p + 1) q k hk ((TotalCup.Cech.total R X N).d p (p + 1) x) y := by
  have h := TotalLeibniz.CechCup.differential_totalCup R X N p q x y
  rw [hy, map_zero, smul_zero, add_zero] at h
  have ht : p + q + 1 = k := by omega
  exact (totalDegreeCast_d_target R X N ht _).symm.trans
    ((congrArg (TotalComponents.CechCup.totalDegreeCast R X N ht) h).trans
      (totalDegreeCast_cupInto R X N ht (by omega) _ _))

theorem differential_totalCup_left_closed (p q k : ℕ) (hk : p + (q + 1) = k)
    (x : (TotalCup.Cech.total R X N).X p) (y : (TotalCup.Cech.total R X N).X q)
    (hx : (TotalCup.Cech.total R X N).d p (p + 1) x = 0) :
    (TotalCup.Cech.total R X N).d (p + q) k ((-1 : ℤ) ^ p • TotalCup.Cech.totalCup R X N p q x y) =
      TotalComponents.CechCup.cupInto R X N p (q + 1) k hk x ((TotalCup.Cech.total R X N).d q (q + 1) y) := by
  have h := TotalLeibniz.CechCup.differential_totalCup R X N p q x y
  rw [hx, map_zero, LinearMap.zero_apply, zero_add] at h
  have hs : (TotalCup.Cech.total R X N).d (p + q) (p + q + 1) ((-1 : ℤ) ^ p • TotalCup.Cech.totalCup R X N p q x y) =
      TotalComponents.CechCup.cupInto R X N p (q + 1) (p + q + 1) (by omega) x ((TotalCup.Cech.total R X N).d q (q + 1) y) := by
    rw [map_zsmul, h, smul_smul, ← mul_pow]
    simp only [neg_mul_neg, one_mul, one_pow, one_smul]
  have ht : p + q + 1 = k := by omega
  exact (totalDegreeCast_d_target R X N ht _).symm.trans
    ((congrArg (TotalComponents.CechCup.totalDegreeCast R X N ht) hs).trans
      (totalDegreeCast_cupInto R X N ht (by omega) _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.TotalBoundaries.CechCup
