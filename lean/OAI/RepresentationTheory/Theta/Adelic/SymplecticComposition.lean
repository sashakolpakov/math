import OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction
import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

/-! # Symplectic Composition -/

namespace OAI.RepresentationTheory.Theta.Adelic.SymplecticComposition

noncomputable section

/-! The actual coordinate actions form a representation; the constructed
Siegel blocks therefore satisfy the full matrix composition law. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.IntrinsicGeometricAction.Intrinsic OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.IntrinsicPhaseIntertwining OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates.Symplectic OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Siegel
open OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction

theorem tensorLinear_mul {k : Type} [Field k] {d : k} {n m : ℕ}
    (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (g h : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K) (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K (g * h) x = Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K g (Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K h x) := by
  simp [Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear, map_mul, Matrix.mulVec_mulVec]

theorem tensorLinear_one {k : Type} [Field k] {d : k} {n m : ℕ}
    (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (K : Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)) (x : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d n m) :
    Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear H K 1 x = x := by simp [Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear]

section Matrices
variable {I : Type} [Fintype I] [DecidableEq I]
variable (e f h : ((I ⊕ I) → ℝ) ≃ₗ[ℝ] ((I ⊕ I) → ℝ))
variable (he : ∀ x y, DataTheta.standardPairing (e x) (e y) = DataTheta.standardPairing x y)
variable (hf : ∀ x y, DataTheta.standardPairing (f x) (f y) = DataTheta.standardPairing x y)
variable (hh : ∀ x y, DataTheta.standardPairing (h x) (h y) = DataTheta.standardPairing x y)

theorem linear_blocks_mul (hm : ∀ x, h x = e (f x)) :
    PoissonAutomorphyNormalizationData.blocks (BilinearCoordinates.Symplectic.linearSymplectic h hh) =
      PoissonAutomorphyGaussianParabolic.Construction.composeBlocks (PoissonAutomorphyNormalizationData.blocks (BilinearCoordinates.Symplectic.linearSymplectic e he))
        (PoissonAutomorphyNormalizationData.blocks (BilinearCoordinates.Symplectic.linearSymplectic f hf)) := by
  rw [← PoissonAutomorphyGaussianParabolic.Construction.blocks_mul]
  congr 1
  apply Subtype.ext
  change LinearMap.toMatrix' h.toLinearMap =
    LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' f.toLinearMap
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact hm x

theorem linear_blocks_one (hm : ∀ x, e x = x) :
    DataTheta.blockMatrix (PoissonAutomorphyNormalizationData.blocks (BilinearCoordinates.Symplectic.linearSymplectic e he)) = 1 := by
  rw [BilinearCoordinates.Symplectic.blocks_matrix]
  change LinearMap.toMatrix' e.toLinearMap = 1
  rw [← LinearMap.toMatrix'_id]
  congr 1
  apply LinearMap.ext
  intro x
  exact hm x
end Matrices

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem nativeTensorAction_mul (g h : RationalSU.ArchimedeanSU F H)
    (s : ∀ v : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    IntrinsicGeometricAction.Intrinsic.nativeTensorAction A (g * h) s = IntrinsicGeometricAction.Intrinsic.nativeTensorAction A g (IntrinsicGeometricAction.Intrinsic.nativeTensorAction A h s) := by
  funext v
  dsimp only [IntrinsicGeometricAction.Intrinsic.nativeTensorAction, Pi.mul_apply]
  rw [map_mul, tensorLinear_mul]

theorem nativeTensorAction_one
    (s : ∀ v : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    IntrinsicGeometricAction.Intrinsic.nativeTensorAction A 1 s = s := by
  funext v
  dsimp only [IntrinsicGeometricAction.Intrinsic.nativeTensorAction, Pi.one_apply]
  rw [map_one, tensorLinear_one]

theorem realCoordinateAction_mul (g h : RationalSU.ArchimedeanSU F H)
    (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :
    RealSymplecticAction.realCoordinateAction A P (g * h) x = RealSymplecticAction.realCoordinateAction A P g (RealSymplecticAction.realCoordinateAction A P h x) := by
  obtain ⟨s, rfl⟩ := (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P).surjective x
  rw [ComplexIntrinsicAction.IntrinsicPhaseIntertwining.realCoordinateAction_nativePhase, ComplexIntrinsicAction.IntrinsicPhaseIntertwining.realCoordinateAction_nativePhase,
    ComplexIntrinsicAction.IntrinsicPhaseIntertwining.realCoordinateAction_nativePhase, nativeTensorAction_mul]

theorem realCoordinateAction_one (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :
    RealSymplecticAction.realCoordinateAction A P 1 x = x := by
  obtain ⟨s, rfl⟩ := (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P).surjective x
  rw [ComplexIntrinsicAction.IntrinsicPhaseIntertwining.realCoordinateAction_nativePhase, nativeTensorAction_one]

theorem realSiegelAction_mul (g h : RationalSU.ArchimedeanSU F H)
    (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :
    RealSymplecticAction.realSiegelAction A P (g * h) x = RealSymplecticAction.realSiegelAction A P g (RealSymplecticAction.realSiegelAction A P h x) := by
  simp only [RealSymplecticAction.realSiegelAction, BilinearCoordinates.Symplectic.swapConjugate_apply, ComplexIntrinsicAction.Siegel.swap_swap, realCoordinateAction_mul]

theorem realSiegelAction_one (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :
    RealSymplecticAction.realSiegelAction A P 1 x = x := by
  rw [RealSymplecticAction.realSiegelAction, BilinearCoordinates.Symplectic.swapConjugate_apply, realCoordinateAction_one, ComplexIntrinsicAction.Siegel.swap_swap]

theorem realSymplecticBlocks_mul (g h : RationalSU.ArchimedeanSU F H) :
    RealSymplecticAction.realSymplecticBlocks A P (g * h) =
      PoissonAutomorphyGaussianParabolic.Construction.composeBlocks (RealSymplecticAction.realSymplecticBlocks A P g) (RealSymplecticAction.realSymplecticBlocks A P h) :=
  linear_blocks_mul _ _ _ _ _ _ (realSiegelAction_mul A P g h)

theorem realSymplecticBlocks_one : DataTheta.blockMatrix (RealSymplecticAction.realSymplecticBlocks A P 1) = 1 :=
  linear_blocks_one _ _ (realSiegelAction_one A P)

end

end OAI.RepresentationTheory.Theta.Adelic.SymplecticComposition
