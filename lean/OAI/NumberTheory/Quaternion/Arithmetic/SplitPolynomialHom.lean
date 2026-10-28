import OAI.NumberTheory.Quaternion.Arithmetic.SplitPolynomials
import OAI.NumberTheory.Quaternion.Arithmetic.SplitGroup
import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialCurveTransport
import OAI.NumberTheory.Quaternion.Arithmetic.SpecialLinearAdeles

/-! # Split Polynomial Hom -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SplitPolynomialHom

noncomputable section

/-! A polynomial isomorphism from SL₂ to the norm-one matrix group
of a quaternion algebra split over the ground field. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra

variable {F K : Type} [Field F] [Field K]

theorem quaternion_splitting_equation_map (ρ : F →+* K) (a b x y : F)
    (h : x ^ 2 - a * y ^ 2 = b) : (ρ x) ^ 2 - ρ a * (ρ y) ^ 2 = ρ b := by
  simpa only [map_sub, map_mul, map_pow] using congrArg ρ h

def splitQuaternionMatrixPointsEquiv [CharZero K] (a b x y : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) (ρ : F →+* K) :
    (SpecialLinearAdeles.specialLinearMatrixGroup F 2).Points ρ ≃* (MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ :=
  (Subgroup.topEquiv.trans (SplitGroup.quaternionNormOneSpecialLinearEquiv (ρ a) (ρ b) (ρ x) (ρ y)
    ((map_ne_zero ρ).mpr ha) ((map_ne_zero ρ).mpr hb)
      (quaternion_splitting_equation_map ρ a b x y h)).symm).trans
    (MatrixGroup.quaternionMatrixPointsEquiv a b ρ)

theorem splitQuaternionMatrixPointsEquiv_matrix [CharZero K]
    (a b x y : F) (ha : a ≠ 0) (hb : b ≠ 0) (h : x ^ 2 - a * y ^ 2 = b) (ρ : F →+* K)
    (g : (SpecialLinearAdeles.specialLinearMatrixGroup F 2).Points ρ) :
    PolynomialGaloisNorm.matrixPointsHom (MatrixGroup.quaternionNormOneMatrixGroup a b) ρ
      (splitQuaternionMatrixPointsEquiv a b x y ha hb h ρ g) =
      MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b) (SplitInverse.quaternionSplitInverse (ρ a) (ρ b) (ρ x) (ρ y) g.val.val) := by
  change MatrixQuaternionDet.quaternionRegularMatrix (ρ a) (ρ b)
    ((SplitMatrices.quaternionSplittingEquiv (ρ a) (ρ b) (ρ x) (ρ y)
      ((map_ne_zero ρ).mpr ha) ((map_ne_zero ρ).mpr hb)
        (quaternion_splitting_equation_map ρ a b x y h)).symm g.val.val) = _
  rw [SplitInverse.quaternionSplittingEquiv_symm_apply]

variable [CharZero F]

def splitQuaternionPolynomialHom (a b x y : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) :
    AlgebraicHypotheses.PolynomialHom (SpecialLinearAdeles.specialLinearMatrixGroup F 2) (MatrixGroup.quaternionNormOneMatrixGroup a b) where
  hom K _ ρ := by
    let : CharZero K := charZero_of_injective_ringHom ρ.injective
    exact (splitQuaternionMatrixPointsEquiv a b x y ha hb h ρ).toMonoidHom
  coordinates := SplitPolynomials.quaternionSplitRegularPolynomials a b x y
  coordinate_eq K _ ρ g i j := by
    let : CharZero K := charZero_of_injective_ringHom ρ.injective
    change PolynomialGaloisNorm.matrixPointsHom (MatrixGroup.quaternionNormOneMatrixGroup a b) ρ
      (splitQuaternionMatrixPointsEquiv a b x y ha hb h ρ g) i j = _
    rw [splitQuaternionMatrixPointsEquiv_matrix]
    exact (congrFun (congrFun (SplitPolynomials.quaternionSplitRegularPolynomials_eval ρ a b x y g.val.val) i) j).symm

theorem splitQuaternionPolynomialHom_surjective (a b x y : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) (ρ : F →+* K) :
    Function.Surjective ((splitQuaternionPolynomialHom a b x y ha hb h).hom K ρ) := by
  let : CharZero K := charZero_of_injective_ringHom ρ.injective
  exact (splitQuaternionMatrixPointsEquiv a b x y ha hb h ρ).surjective

end

end OAI.NumberTheory.Quaternion.Arithmetic.SplitPolynomialHom
