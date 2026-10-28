import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianValues

/-! # Intrinsic Local Gaussian Action -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianAction.Intrinsic

noncomputable section

/-! Local normalized values of the actual native SU oscillator action,
extracted from the complete product covariance. This supplies actual
local operator formulas for phase-space action recovery. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianValues.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem local_gaussian_from_product (φ : Adelic.ThetaEvaluation.ArchimedeanTests F (3 * m))
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hval : ∀ x : Adelic.BallGeometryData.RealPositions A, Adelic.DataTheta.archTestValue (A := A) φ x = c * Adelic.DataTheta.gaussianValue Z.matrix ξ (B.realPosition x)) :
    (∀ v : Fin A.places, (φ (A.enumerate v)).val 0 ≠ 0) ∧
      ∀ (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)),
        ((φ (A.enumerate v)).val 0)⁻¹ * (φ (A.enumerate v)).val (fun i => (A.real v).symm (x i)) =
          IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v Z).matrix (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v ξ) x := by
  let f : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m) → ℂ := fun w y =>
    (φ (A.enumerate w)).val (fun i => (A.real w).symm (y i))
  have hzero : (∏ w, f w 0) = c := by
    have hz := hval 0
    simp [Adelic.DataTheta.archTestValue,Adelic.DataTheta.gaussianValue] at hz
    dsimp [f]
    simp only [map_zero]
    exact hz
  have hn : ∀ w, f w 0 ≠ 0 := by
    intro w
    exact (Finset.prod_ne_zero_iff.mp (show (∏ w, f w 0) ≠ 0 by rw [hzero]; exact hc)) w (Finset.mem_univ w)
  let g : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m) → ℂ := fun w y => (f w 0)⁻¹ * f w y
  have hgzero (w : Fin A.places) : g w 0 = 1 := inv_mul_cancel₀ (hn w)
  have hgprod : (∏ w, g w 0) = 1 := by simp only [hgzero,Finset.prod_const_one]
  have hgval (y : Adelic.BallGeometryData.RealPositions A) : (∏ w, g w (y w)) = Adelic.DataTheta.gaussianValue Z.matrix ξ (B.realPosition y) := by
    change (∏ w, (f w 0)⁻¹ * f w (y w)) = _
    rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,hzero]
    have hprod : (∏ w, f w (y w)) = c * Adelic.DataTheta.gaussianValue Z.matrix ξ (B.realPosition y) := hval y
    rw [hprod,← mul_assoc,inv_mul_cancel₀ hc,one_mul]
  refine ⟨?_,?_⟩
  · intro v
    have hv := hn v
    simp [f] at hv
    exact hv
  · intro v x
    have he := IntrinsicLocalGaussianValues.Intrinsic.product_single_ratio g hgprod v x
    rw [hgzero,one_mul,hgval] at he
    simp [g,f] at he
    exact he.trans (by
      unfold Adelic.DataTheta.gaussianValue IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian
      rw [IntrinsicLocalGaussianCoordinates.Intrinsic.local_gaussian_quadratic,IntrinsicLocalGaussianCoordinates.Intrinsic.local_gaussian_linear])

variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P}

theorem native_local_action_gaussian (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    let φ := Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (B.gaussian z ξ)
    (∀ v : Fin A.places, (φ (A.enumerate v)).val 0 ≠ 0) ∧
      ∀ (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)),
        ((φ (A.enumerate v)).val 0)⁻¹ * (φ (A.enumerate v)).val (fun i => (A.real v).symm (x i)) =
          IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period (B.ball g • z))).matrix
            (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v ((B.symplectic g).jacobiChange (B.period z) ξ)) x := by
  apply local_gaussian_from_product B _ _ _
    ((Adelic.DataTheta.oscillatorFactor B P hd C D g z)⁻¹ * Complex.exp (-(B.symplectic g).thetaCorrectionForm (B.period z) ξ ξ))
    (mul_ne_zero (inv_ne_zero (hO.2.2.1 g z).1) (Complex.exp_ne_zero _))
  exact hO.2.2.2.2.2.2.2.1 g z ξ

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianAction.Intrinsic
