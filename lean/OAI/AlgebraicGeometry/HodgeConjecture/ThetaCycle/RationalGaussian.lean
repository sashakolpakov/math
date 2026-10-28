import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelGaussian
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCharacterNormalization
import OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
import OAI.RepresentationTheory.Theta.Kernel.Definitions

/-! # Rational Gaussian -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalGaussian.CM

noncomputable section

/-! ThetaCycle: the classical Siegel Gaussian in the actual rational
archimedean completion and its exact values on principal rational points. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.Completion
open OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

def realCompletionPositionEquiv {F : Type} [Field F] (N : ℕ)
    (v : InfinitePlace F) (hv : v.IsReal) :
    (Fin N → ℝ) ≃ₜ+ (Fin N → v.Completion) where
  toFun x i := (ringEquivRealOfIsReal hv).symm (x i)
  invFun x i := ringEquivRealOfIsReal hv (x i)
  left_inv x := funext (fun i => (ringEquivRealOfIsReal hv).apply_symm_apply (x i))
  right_inv x := funext (fun i => (ringEquivRealOfIsReal hv).symm_apply_apply (x i))
  map_add' x y := funext (fun i => (ringEquivRealOfIsReal hv).symm.map_add (x i) (y i))
  continuous_toFun := continuous_pi (fun i =>
    (isometryEquivRealOfIsReal hv).symm.continuous.comp (continuous_apply i))
  continuous_invFun := continuous_pi (fun i =>
    (isometryEquivRealOfIsReal hv).continuous.comp (continuous_apply i))

def realCompletionGaussian {F : Type} [Field F] (N : ℕ) (v : InfinitePlace F) (hv : v.IsReal)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat v.Completion N :=
  ⟨fun x => SiegelGaussian.CM.siegelGaussianSchwartz Z z ((realCompletionPositionEquiv N v hv).symm x),
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem (realCompletionPositionEquiv N v hv) (SiegelGaussian.CM.siegelGaussianSchwartz Z z)⟩

theorem real_completion_gaussian_apply {F : Type} [Field F] (N : ℕ)
    (v : InfinitePlace F) (hv : v.IsReal) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ)
    (x : Fin N → v.Completion) :
    (realCompletionGaussian N v hv Z z).val x =
      RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z (fun i => ringEquivRealOfIsReal hv (x i)) :=
  SiegelGaussian.CM.siegel_gaussian_schwartz_apply Z z _

def rationalArchimedeanGaussian (N : ℕ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests ℚ N :=
  fun v => realCompletionGaussian N v (IsTotallyReal.isReal v) Z z

theorem rational_gaussian_local_principal (N : ℕ) (v : InfinitePlace ℚ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) (q : Fin N → ℚ) :
    (rationalArchimedeanGaussian N Z z v).val
        (fun i => RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar ℚ (.inl v) (q i)) =
      RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z (fun i => (q i : ℝ)) := by
  rw [rationalArchimedeanGaussian, real_completion_gaussian_apply]
  congr 1
  funext i
  exact (ringEquivRealOfIsReal (IsTotallyReal.isReal v)).toRingHom.map_rat_algebraMap (q i)

theorem rational_gaussian_archimedean_value (N : ℕ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N))
    (z : Fin N → ℂ) (q : Fin N → ℚ) :
    RepresentationTheory.Theta.Adelic.ThetaEvaluation.archimedeanValue ℚ N (rationalArchimedeanGaussian N Z z) q =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel Z.matrix q z := by
  unfold RepresentationTheory.Theta.Adelic.ThetaEvaluation.archimedeanValue
  rw [Fintype.prod_unique, rational_gaussian_local_principal]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalGaussian.CM
