import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.AdditionBundle

/-! # Addition Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every tensor power of the actual addition-graph bundle has the
uniform Euler polynomial dictated by its quadratic class. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u
variable {k : Type u} [Field k] {g : ℕ} {A₀ : Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (D : Dual.Data.DualAbelianData A₀) (p : A₀.scheme ⟶ D.abelian.scheme) [IsMonHom p]

theorem Polarization.AdditionPowers.polarizationSquareClass_pow (a b c : ℤ) (m : ℕ) :
    Polarization.ShearClasses.polarizationSquareClass D p a b c ^ m =
      Polarization.ShearClasses.polarizationSquareClass D p (a * (m : ℤ)) (b * (m : ℤ)) (c * (m : ℤ)) := by
  unfold Polarization.ShearClasses.polarizationSquareClass
  rw [mul_pow, mul_pow]
  simp only [← zpow_natCast, ← zpow_mul]

variable {N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (L : Line.Bundles.LineBundle A.abelian.scheme.left)
variable (e : (((A.dual.poincareAt A.polarization.isogeny.hom).tensor
  (L.pullback (fst A.abelian.scheme A.abelian.scheme).left)).tensor
    (L.pullback (snd A.abelian.scheme A.abelian.scheme).left)).sheaf ≅
  (L.pullback μ[A.abelian.scheme].left).sheaf)

include L e in
theorem PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_tensorPower_class (m : ℕ) :
    Line.Bundles.LineBundle.classOf (A.additionGraphBundle.tensorPower m) =
      Polarization.ShearClasses.polarizationSquareClass A.dual A.polarization.isogeny.hom
        (2 * (m : ℤ)) (2 * (m : ℤ)) (2 * (m : ℤ)) := by
  rw [Line.Bundles.LineBundle.classOf_tensorPower, A.additionGraphBundle_class L e, Polarization.AdditionPowers.polarizationSquareClass_pow]

include L e in
theorem PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_tensorPower_euler
    (hN : 3 ≤ N) (hNk : (N : k) ≠ 0) (m : ℕ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.abelian.scheme ⊗ A.abelian.scheme).hom
      (A.additionGraphBundle.tensorPower m).sheaf =
      (3 : ℤ) ^ g * (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf) ^ 2 *
        (m : ℤ) ^ (2 * g) := by
  have h := A.polarizationSquareClass_euler_determinant_of_normalized_formula hN hNk L e
    (2 * (m : ℤ)) (2 * (m : ℤ)) (2 * (m : ℤ))
  rw [← A.additionGraphBundle_tensorPower_class L e m, LineBundle.EulerShifts.lineBundleClassEuler_classOf] at h
  have hq : (4 : ℚ) * ((2 * (m : ℤ) : ℤ) : ℚ) * ((2 * (m : ℤ) : ℤ) : ℚ) -
      ((2 * (m : ℤ) : ℤ) : ℚ) ^ 2 = 12 * (m : ℚ) ^ 2 := by
    push_cast
    ring
  rw [hq, mul_pow, ← pow_mul] at h
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  apply mul_left_cancel₀ (pow_ne_zero g (show (4 : ℚ) ≠ 0 by norm_num))
  exact h.trans (by
    rw [show (12 : ℚ) = 4 * 3 by norm_num, mul_pow]
    ring)

include L e in
theorem PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_tensorPower_euler_normalized
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : k) ≠ 0) (m : ℕ) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.abelian.scheme ⊗ A.abelian.scheme).hom
      (A.additionGraphBundle.tensorPower m).sheaf =
      (3 : ℤ) ^ g * ((2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ)) ^ 2 * (m : ℤ) ^ (2 * g) := by
  rw [A.additionGraphBundle_tensorPower_euler L e hN hNk,
    A.graphBundle_euler_normalized_overField hg hN hNk]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
