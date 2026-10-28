import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.SquareEulerDeterminant
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphPolynomial

/-! # Addition Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.AdditionBundle.PolarizedAbelianWithLevel

noncomputable section

/-! The external graph bundles and the pullback along addition form the
actual line bundle underlying the addition graph. Its Euler coefficient
is three to the relative dimension times the square of the graph coefficient. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    Line.Bundles.LineBundle (A.abelian.scheme ⊗ A.abelian.scheme).left :=
  ((A.graphBundle.pullback (fst A.abelian.scheme A.abelian.scheme).left).tensor
    (A.graphBundle.pullback (snd A.abelian.scheme A.abelian.scheme).left)).tensor
      (A.graphBundle.pullback μ[A.abelian.scheme].left)

variable {k : Type u} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (L : Line.Bundles.LineBundle A.abelian.scheme.left)
variable (e : (((A.dual.poincareAt A.polarization.isogeny.hom).tensor
  (L.pullback (fst A.abelian.scheme A.abelian.scheme).left)).tensor
    (L.pullback (snd A.abelian.scheme A.abelian.scheme).left)).sheaf ≅
  (L.pullback μ[A.abelian.scheme].left).sheaf)

private theorem pairDiagonalMul {G A : Type*} [Monoid G] [CommMonoid A]
    (B : G →* G →* A) (x y : G) (h : B y x = B x y) :
    B (x * y) (x * y) = B x x * B y y * B x y ^ 2 := by
  rw [B.map_mul]
  change B x (x * y) * B y (x * y) = _
  rw [(B x).map_mul, (B y).map_mul, h, pow_two]
  ac_rfl

private theorem pairDiagonalProduct {G C : Type*} [Monoid G] [CommGroup C]
    (B : G →* G →* C) (x y : G) (h : B y x = B x y) :
    (B x x * B y y) * B (x * y) (x * y) =
      B x x ^ (2 : ℤ) * B y y ^ (2 : ℤ) * B x y ^ (2 : ℤ) := by
  rw [pairDiagonalMul B x y h]
  simp only [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
  rw [← mul_assoc, ← pow_two, mul_pow]

include L e in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_class :
    Line.Bundles.LineBundle.classOf A.additionGraphBundle =
      ShearClasses.polarizationSquareClass A.dual A.polarization.isogeny.hom 2 2 2 := by
  let B := ClassPairing.polarizationPairClass A.dual A.polarization.isogeny.hom
    (A.abelian.scheme ⊗ A.abelian.scheme)
  let x := fst A.abelian.scheme A.abelian.scheme
  let y := snd A.abelian.scheme A.abelian.scheme
  have hμ : x * y = μ[A.abelian.scheme] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hs := PairSymmetry.polarizationPairClass_symmetric A.dual A.polarization.isogeny.hom L e y x
  change Line.Bundles.LineBundle.classOf (((A.graphBundle.pullback x.left).tensor
    (A.graphBundle.pullback y.left)).tensor (A.graphBundle.pullback μ[A.abelian.scheme].left)) = _
  simp only [PolarizationData.PolarizedAbelianWithFullLevel.graphBundle]
  rw [Line.Bundles.LineBundle.classOf_tensor, Line.Bundles.LineBundle.classOf_tensor,
    ClassPairing.graphPullback_class_eq_pair, ClassPairing.graphPullback_class_eq_pair, ClassPairing.graphPullback_class_eq_pair]
  change B x x * B y y * B μ[A.abelian.scheme] μ[A.abelian.scheme] =
    B x x ^ (2 : ℤ) * B y y ^ (2 : ℤ) * B x y ^ (2 : ℤ)
  rw [← hμ]
  exact pairDiagonalProduct B x y hs

include L e in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_euler (hN : 3 ≤ N) (hNk : (N : k) ≠ 0) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.abelian.scheme ⊗ A.abelian.scheme).hom
      A.additionGraphBundle.sheaf =
    (3 : ℤ) ^ g * (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf) ^ 2 := by
  have h := A.polarizationSquareClass_euler_determinant_of_normalized_formula hN hNk L e 2 2 2
  rw [← A.additionGraphBundle_class L e, LineBundle.EulerShifts.lineBundleClassEuler_classOf] at h
  norm_num at h
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  apply mul_left_cancel₀ (pow_ne_zero g (show (4 : ℚ) ≠ 0 by norm_num))
  calc
    _ = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf : ℚ) ^ 2 *
        (12 : ℚ) ^ g := h
    _ = _ := by
      rw [show (12 : ℚ) = 4 * 3 by norm_num, mul_pow]
      ring

include L e in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.additionGraphBundle_euler_normalized
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : k) ≠ 0) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.abelian.scheme ⊗ A.abelian.scheme).hom
      A.additionGraphBundle.sheaf =
      (3 : ℤ) ^ g * ((2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ)) ^ 2 := by
  rw [A.additionGraphBundle_euler L e hN hNk,
    A.graphBundle_euler_normalized_overField hg hN hNk]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.AdditionBundle.PolarizedAbelianWithLevel
