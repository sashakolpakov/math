import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianPlaceOrthogonality

/-! # Intrinsic Place Pairing -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlacePairing.Intrinsic

noncomputable section

/-! Actual place projections are self-adjoint for the native trace
pairing. The full Gaussian product law gives the corresponding
balance identity for the positive period form. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianPlaceOrthogonality.Intrinsic

theorem place_pairing_balance {V I k : Type} [Fintype V] [DecidableEq V] [Fintype I] [Field k]
    (v : V) (x y : V → (I ⊕ I) → k) :
    (∑ w, Adelic.DataTheta.standardPairing ((Pi.single v (x v) : V → (I ⊕ I) → k) w) (y w)) =
      ∑ w, Adelic.DataTheta.standardPairing (x w) ((Pi.single v (y v) : V → (I ⊕ I) → k) w) := by
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w = v
  · subst w
    rw [Pi.single_eq_same,Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne hw,Adelic.DataTheta.standardPairing]

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem native_place_pairing_balance (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (v : Fin A.places) (x y : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) :
    Adelic.DataTheta.standardPairing (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v x) y = Adelic.DataTheta.standardPairing x (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v y) := by
  have hl := hC.2.2.2.2.2.1 (Pi.single v (B.realPhase.symm x v)) (B.realPhase.symm y)
  have hr := hC.2.2.2.2.2.1 (B.realPhase.symm x) (Pi.single v (B.realPhase.symm y v))
  rw [B.realPhase.apply_symm_apply] at hl hr
  exact hl.trans ((place_pairing_balance v (B.realPhase.symm x) (B.realPhase.symm y)).trans hr.symm)

theorem native_period_place_balance {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
    {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (z : Adelic.BallNatural.Ball)
    (v : Fin A.places) (x y : Adelic.BallGeometryData.RealPositions A) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix (B.realPosition (Pi.single v (x v))) (B.realPosition y) =
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix (B.realPosition x) (B.realPosition (Pi.single v (y v))) := by
  rw [IntrinsicGaussianPlaceOrthogonality.Intrinsic.native_gaussian_bilinear_sum B hO,IntrinsicGaussianPlaceOrthogonality.Intrinsic.native_gaussian_bilinear_sum B hO]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w = v
  · subst w
    rw [Pi.single_eq_same,Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hw,map_zero,zero_apply]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlacePairing.Intrinsic
