import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicOscillatorBranch
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicGaussianCovariance

/-! # Intrinsic Oscillator Identification -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicOscillatorIdentification.CM

noncomputable section

/-! Full native oscillator identification: every Gaussian, double-cover,
regularity, cocycle, Jacobi, and natural-line clause is proved. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)
  (hd : d ≠ 0) (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 m)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 m H W hd C P) (hC : C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F)

include hC in
theorem native_oscillator_identification :
    RepresentationTheory.Theta.Adelic.DataTheta.OscillatorIdentification (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P) P hd C D := by
  refine ⟨IntrinsicGaussianCoordinates.CM.native_gaussian_product_coordinates A P, IntrinsicArchimedeanLift.CM.native_real_splitting_metaplectic A P hd C D,
    IntrinsicGaussianCocycle.CM.native_oscillator_factor_square A P hd C D hC,
    IntrinsicOscillatorBranch.CM.native_oscillator_factor_holomorphic A P hd C D hC,
    IntrinsicOscillatorBranch.CM.native_oscillator_factor_continuous A P hd C D hC,
    IntrinsicGaussianCocycle.CM.native_oscillator_factor_mul A P hd C D hC, IntrinsicGaussianCocycle.CM.native_oscillator_factor_one A P hd C D,
    IntrinsicGaussianCovariance.CM.native_full_gaussian_covariance A P hd C D hC, IntrinsicOscillatorBranch.CM.native_oscillator_factor_natural A P hd C D hC, ?_⟩
  intro χ g
  exact BallPerfect.CM.ball_group_character_eq_one χ.toMonoidHom g

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicOscillatorIdentification.CM
