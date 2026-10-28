import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness

/-! # Intrinsic Local Gaussian Values -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianValues.Intrinsic

noncomputable section

/-! Extract actual local Gaussian values from the full native product
identity. Normalizing by the local value at zero removes arbitrary
representative scalars without assuming regularity of those choices. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg

theorem product_single_ratio {I X : Type} [Fintype I] [DecidableEq I] [Zero X]
    (f : I → X → ℂ) (h : ∏ i, f i 0 = 1) (v : I) (x : X) :
    f v x = f v 0 * ∏ i, f i ((Pi.single v x : I → X) i) := by
  have hn : ∀ i, f i 0 ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp (show (∏ i, f i 0) ≠ 0 by rw [h]; exact one_ne_zero)) i
      (Finset.mem_univ i)
  have he : (∏ i, f i ((Pi.single v x : I → X) i)) / (∏ i, f i 0) = f v x / f v 0 := by
    rw [← Finset.prod_div_distrib]
    calc
      _ = f v ((Pi.single v x : I → X) v) / f v 0 := by
        apply Finset.prod_eq_single v
        · intro i _ hiv
          simp [hiv,hn i]
        · simp
      _ = _ := by rw [Pi.single_eq_same]
  rw [h,div_one] at he
  exact ((div_eq_iff (hn v)).mp he.symm).trans (mul_comm _ _)

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H K hd C P}

theorem native_gaussian_zero_product (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (z : Adelic.BallNatural.Ball) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (∏ v : Fin A.places, ((B.gaussian z ξ) (A.enumerate v)).val 0) = 1 := by
  have h := hO.1 z ξ 0
  simp [Adelic.DataTheta.archTestValue,Adelic.DataTheta.gaussianValue] at h
  exact h

theorem native_local_gaussian_zero_ne (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (z : Adelic.BallNatural.Ball) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) (v : Fin A.places) :
    ((B.gaussian z ξ) (A.enumerate v)).val 0 ≠ 0 := by
  have h := native_gaussian_zero_product B hO z ξ
  exact (Finset.prod_ne_zero_iff.mp (show
      (∏ w : Fin A.places, ((B.gaussian z ξ) (A.enumerate w)).val 0) ≠ 0 by rw [h]; exact one_ne_zero)) v
    (Finset.mem_univ v)

theorem native_local_gaussian_value (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (z : Adelic.BallNatural.Ball) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    ((B.gaussian z ξ) (A.enumerate v)).val (fun i => (A.real v).symm (x i)) =
      ((B.gaussian z ξ) (A.enumerate v)).val 0 *
        Adelic.DataTheta.gaussianValue (B.period z).matrix ξ (B.realPosition (Pi.single v x)) := by
  let f : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m) → ℂ := fun w y =>
    ((B.gaussian z ξ) (A.enumerate w)).val (fun i => (A.real w).symm (y i))
  have hp : (∏ w, f w 0) = 1 := by
    dsimp [f]
    simp only [map_zero]
    exact native_gaussian_zero_product B hO z ξ
  have he := product_single_ratio f hp v x
  have hg : (∏ w, f w ((Pi.single v x : Adelic.BallGeometryData.RealPositions A) w)) =
      Adelic.DataTheta.gaussianValue (B.period z).matrix ξ (B.realPosition (Pi.single v x)) := hO.1 z ξ (Pi.single v x)
  rw [hg] at he
  simp [f] at he
  exact he

theorem normalized_local_gaussian_value (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (z : Adelic.BallNatural.Ball) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    (((B.gaussian z ξ) (A.enumerate v)).val 0)⁻¹ *
      ((B.gaussian z ξ) (A.enumerate v)).val (fun i => (A.real v).symm (x i)) =
        IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianPeriod B v (B.period z)).matrix (IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v ξ) x := by
  rw [native_local_gaussian_value B hO z ξ v x,← mul_assoc,
    inv_mul_cancel₀ (native_local_gaussian_zero_ne B hO z ξ v),one_mul]
  unfold Adelic.DataTheta.gaussianValue IntrinsicGaussianUniqueness.IntrinsicHeisenberg.jacobiGaussian
  rw [IntrinsicLocalGaussianCoordinates.Intrinsic.local_gaussian_quadratic,IntrinsicLocalGaussianCoordinates.Intrinsic.local_gaussian_linear]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianValues.Intrinsic
