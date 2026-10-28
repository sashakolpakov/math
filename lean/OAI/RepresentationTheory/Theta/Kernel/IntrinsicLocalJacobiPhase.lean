import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianPlaceOrthogonality
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalPositionBlocks

/-! # Intrinsic Local Jacobi Phase -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic

noncomputable section

/-! The Jacobi parameter in actual native position coordinates restricts
to the ordinary position/momentum parameter at every real place. The
period compatibility is derived from the full Gaussian product law. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalPositionBlocks.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianPlaceOrthogonality.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg

theorem siegel_form_mulVec {I : Type*} [Fintype I]
    (Z : Matrix I I ℂ) (x y : I → ℝ) :
    (∑ i, (x i : ℂ) * Z.mulVec (fun j => (y j : ℂ)) i) = AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z x y := by
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P}

theorem local_period_position (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (z : Adelic.BallNatural.Ball) (v : Fin A.places) (q : Adelic.BallGeometryData.RealPositions A) :
    IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v ((B.period z).matrix.mulVec (fun i => (B.realPosition q i : ℂ))) =
      (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)).matrix.mulVec (fun i => (q v i : ℂ)) := by
  funext j
  have he := IntrinsicLocalGaussianCoordinates.Intrinsic.local_gaussian_linear B v
    ((B.period z).matrix.mulVec (fun i => (B.realPosition q i : ℂ))) (Pi.single j 1)
  rw [siegel_form_mulVec,IntrinsicGaussianPlaceOrthogonality.Intrinsic.native_gaussian_bilinear_sum B hO z] at he
  have hr : (∑ w : Fin A.places,
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B w (B.period z)).matrix
        ((Pi.single v (Pi.single j 1) : Adelic.BallGeometryData.RealPositions A) w) (q w)) =
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)).matrix (Pi.single j 1) (q v) := by
    rw [Finset.sum_eq_single v]
    · rw [Pi.single_eq_same]
    · intro w _ hw
      rw [Pi.single_eq_of_ne hw]
      simp only [map_zero,zero_apply]
    · simp
  rw [hr,← siegel_form_mulVec] at he
  have hcast : (fun i => ((Pi.single j 1 : Fin (3 * m) → ℝ) i : ℂ)) = Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst i
      simp only [Pi.single_eq_same,Complex.ofReal_one]
    · simp only [Pi.single_eq_of_ne hi,Complex.ofReal_zero]
  change (fun i => ((Pi.single j 1 : Fin (3 * m) → ℝ) i : ℂ)) ⬝ᵥ _ =
    (fun i => ((Pi.single j 1 : Fin (3 * m) → ℝ) i : ℂ)) ⬝ᵥ _ at he
  rw [hcast,single_dotProduct,single_dotProduct,one_mul,one_mul] at he
  exact he

def globalRealMomentum (p : Adelic.BallGeometryData.RealPositions A) : Adelic.BallGeometryData.FrameIndex A → ℝ :=
  ∑ v : Fin A.places, (IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B v)ᵀ.mulVec (p v)

theorem global_momentum_real (p : Adelic.BallGeometryData.RealPositions A) :
    IntrinsicLocalPositionBlocks.Intrinsic.globalMomentum B (fun v i => (p v i : ℂ)) = fun i => (globalRealMomentum B p i : ℂ) := by
  unfold IntrinsicLocalPositionBlocks.Intrinsic.globalMomentum globalRealMomentum
  funext i
  simp only [Finset.sum_apply,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact (Complex.ofRealHom.map_mulVec (IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B v)ᵀ (p v) i).symm

theorem local_phase_parameter (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (z : Adelic.BallNatural.Ball) (v : Fin A.places) (q p : Adelic.BallGeometryData.RealPositions A) :
    IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v
      ((fun i => (globalRealMomentum B p i : ℂ)) -
        (B.period z).matrix.mulVec (fun i => (B.realPosition q i : ℂ))) =
      IntrinsicGaussianUniqueness.IntrinsicHeisenberg.realJacobi (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)).matrix (q v) (p v) := by
  rw [← global_momentum_real]
  change ((IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B v).map Complex.ofRealHom)ᵀ.mulVec (_ - _) = _
  rw [Matrix.mulVec_sub]
  change IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v (IntrinsicLocalPositionBlocks.Intrinsic.globalMomentum B (fun w i => (p w i : ℂ))) -
    IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v ((B.period z).matrix.mulVec (fun i => (B.realPosition q i : ℂ))) = _
  rw [IntrinsicLocalPositionBlocks.Intrinsic.local_momentum_component,local_period_position B hO]
  rfl

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic
