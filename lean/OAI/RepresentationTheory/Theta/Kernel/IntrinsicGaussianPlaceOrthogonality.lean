import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianValues
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness

/-! # Intrinsic Gaussian Place Orthogonality -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianPlaceOrthogonality.Intrinsic

noncomputable section

/-! The full native Gaussian product identity forces the actual
quadratic form to split over archimedean places. This is derived for
arbitrary native comparison coordinates. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianValues.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicQuadratic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P}

theorem native_gaussian_local_product (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (z : Adelic.BallNatural.Ball) (x : Adelic.BallGeometryData.RealPositions A) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix (B.realPosition x) (B.realPosition x)) =
      ∏ v : Fin A.places, Complex.exp ((Real.pi : ℂ) * Complex.I *
        AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)).matrix (x v) (x v)) := by
  have hg := hO.1 z 0 x
  simp only [Adelic.DataTheta.gaussianValue,Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero] at hg
  calc
    _ = Adelic.DataTheta.archTestValue (A := A) (B.gaussian z 0) x := hg.symm
    _ = ∏ v : Fin A.places, ((B.gaussian z 0) (A.enumerate v)).val 0 *
        Adelic.DataTheta.gaussianValue (B.period z).matrix 0 (B.realPosition (Pi.single v (x v))) := by
      apply Finset.prod_congr rfl
      intro v _
      exact IntrinsicLocalGaussianValues.Intrinsic.native_local_gaussian_value B hO z 0 v (x v)
    _ = (∏ v : Fin A.places, ((B.gaussian z 0) (A.enumerate v)).val 0) *
        ∏ v : Fin A.places, Adelic.DataTheta.gaussianValue (B.period z).matrix 0 (B.realPosition (Pi.single v (x v))) :=
      Finset.prod_mul_distrib
    _ = _ := by
      rw [IntrinsicLocalGaussianValues.Intrinsic.native_gaussian_zero_product B hO z 0,one_mul]
      apply Finset.prod_congr rfl
      intro v _
      simp only [Adelic.DataTheta.gaussianValue,Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero]
      rw [IntrinsicLocalGaussianCoordinates.Intrinsic.local_gaussian_quadratic]

theorem native_gaussian_bilinear_sum (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (z : Adelic.BallNatural.Ball) (x y : Adelic.BallGeometryData.RealPositions A) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix (B.realPosition x) (B.realPosition y) =
      ∑ v : Fin A.places, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)).matrix (x v) (y v) := by
  let c : ℂ := (Real.pi : ℂ) * Complex.I
  let Q : Adelic.BallGeometryData.RealPositions A →L[ℝ] Adelic.BallGeometryData.RealPositions A →L[ℝ] ℂ := c •
    (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix).bilinearComp B.realPosition.toContinuousLinearMap B.realPosition.toContinuousLinearMap
  let R : Adelic.BallGeometryData.RealPositions A →L[ℝ] Adelic.BallGeometryData.RealPositions A →L[ℝ] ℂ :=
    ∑ v : Fin A.places, c • (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)).matrix).bilinearComp
      (ContinuousLinearMap.proj v) (ContinuousLinearMap.proj v)
  have hQval (u v : Adelic.BallGeometryData.RealPositions A) : Q u v =
      c * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix (B.realPosition u) (B.realPosition v) := rfl
  have hRval (u v : Adelic.BallGeometryData.RealPositions A) : R u v =
      ∑ w, c * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B w (B.period z)).matrix (u w) (v w) := by
    simp [R]
  have hQ (u v : Adelic.BallGeometryData.RealPositions A) : Q u v = Q v u := by
    change c * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix (B.realPosition u) (B.realPosition v) =
      c * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix (B.realPosition v) (B.realPosition u)
    rw [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_symmetric _ (B.period z).symmetric]
  have hR (u v : Adelic.BallGeometryData.RealPositions A) : R u v = R v u := by
    rw [hRval,hRval]
    apply Finset.sum_congr rfl
    intro w _
    rw [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_symmetric _ (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B w (B.period z)).symmetric]
  have he : Q = R := IntrinsicGaussianUniqueness.IntrinsicQuadratic.gaussian_bilinear_unique Q R hQ hR (by
    intro u
    rw [hQval,hRval,Complex.exp_sum]
    exact native_gaussian_local_product B hO z u)
  have hv := congrArg (fun T : Adelic.BallGeometryData.RealPositions A →L[ℝ] Adelic.BallGeometryData.RealPositions A →L[ℝ] ℂ => T x y) he
  rw [hQval,hRval,← Finset.mul_sum] at hv
  exact mul_left_cancel₀ (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero) hv

theorem native_gaussian_different_places (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (z : Adelic.BallNatural.Ball) (v w : Fin A.places) (hvw : v ≠ w) (x y : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix (B.realPosition (Pi.single v x)) (B.realPosition (Pi.single w y)) = 0 := by
  rw [native_gaussian_bilinear_sum B hO z]
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : u = v
  · subst u
    simp [hvw]
  · simp [hu]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianPlaceOrthogonality.Intrinsic
