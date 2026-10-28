import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointCoordinateCoefficientChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange

/-! # Point Polynomial Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointPolynomialCoefficientNaturality

noncomputable section

/-! The inverse polynomial map of a point-coordinate action
commutes with literal coefficient extension. -/
open scoped BigOperators Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] {ι : Type v} [Fintype ι] [DecidableEq ι]

theorem pointCoordinateCoefficientTransform_single_apply
    (T : (ι → R) ≃ₗ[R] (ι → R)) (i j : ι) :
    Dual.CoordinateTransform.pointCoordinateCoefficientTransform T (Finsupp.single j 1) i = T (Pi.single i 1) j := by
  have hf : (Finsupp.llift R R R ι).symm (Finsupp.lapply i) = Pi.single i 1 := by
    funext k
    rw [Finsupp.llift_symm_apply]
    change Finsupp.single k (1 : R) i = (Pi.single i (1 : R) : ι → R) k
    simp only [Finsupp.single_apply, Pi.single_apply, eq_comm]
  have he : Finsupp.llift R R R ι (Pi.single i 1) = Finsupp.lapply i := by
    rw [← hf, LinearEquiv.apply_symm_apply]
  have h := Dual.CoordinateTransform.pointCoordinateCoefficientTransform_values T (Pi.single i 1) j
  rwa [he] at h

theorem pointCoordinateCoefficientTransform_baseChange_single
    (φ : R →+* A) (T : (ι → R) ≃ₗ[R] (ι → R)) (i j : ι) :
    Dual.CoordinateTransform.pointCoordinateCoefficientTransform (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T) (Finsupp.single j 1) i =
      φ (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T (Finsupp.single j 1) i) := by
  rw [pointCoordinateCoefficientTransform_single_apply, pointCoordinateCoefficientTransform_single_apply]
  have hv : (fun k => φ ((Pi.single i (1 : R) : ι → R) k)) = (Pi.single i (1 : A) : ι → A) := by
    funext k
    simp [Pi.single_apply]
  have h := PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv_apply_map φ T (Pi.single i 1)
  rw [hv] at h
  exact congrFun h j

omit [DecidableEq ι] in
theorem linearCoordinatePolynomial_finite_sum (a : ι →₀ R) :
    Linear.CoordinateSubstitution.linearCoordinatePolynomial a = ∑ i : ι, a i • (MvPolynomial.X i : MvPolynomial ι R) := by
  change a.sum (fun i r => r • (MvPolynomial.X i : MvPolynomial ι R)) = _
  exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)

variable {n : ℕ}

theorem pointCoordinateSubstitution_coefficient_natural
    (φ : R →+* A) (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    (MvPolynomial.map φ).comp (Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap).toRingHom =
      (Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform
        (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T)).toLinearMap).toRingHom.comp (MvPolynomial.map φ) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change MvPolynomial.map φ
      (Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap (MvPolynomial.C r)) =
        Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T)).toLinearMap
          (MvPolynomial.map φ (MvPolynomial.C r))
    rw [show Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap (MvPolynomial.C r) =
      MvPolynomial.C r from (Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap).commutes r,
      MvPolynomial.map_C]
    exact ((Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform
      (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T)).toLinearMap).commutes (φ r)).symm
  · intro j
    change MvPolynomial.map φ
      (Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap (MvPolynomial.X j)) =
        Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform (PointCoordinateCoefficientChange.pointCoordinateBaseChangeEquiv φ T)).toLinearMap
          (MvPolynomial.map φ (MvPolynomial.X j))
    rw [MvPolynomial.map_X, Linear.CoordinateSubstitution.polynomialLinearSubstitution_X, Linear.CoordinateSubstitution.polynomialLinearSubstitution_X,
      linearCoordinatePolynomial_finite_sum, linearCoordinatePolynomial_finite_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
    exact congrArg (fun a : A => MvPolynomial.C a * MvPolynomial.X i)
      (pointCoordinateCoefficientTransform_baseChange_single φ T i j).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointPolynomialCoefficientNaturality
