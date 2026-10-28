import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlacePairing
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn

/-! # Intrinsic Period Projection -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPeriodProjection.Intrinsic

noncomputable section

/-! The actual native Gaussian period is balanced by the position
projection to each place. This is derived from the full Gaussian law. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlacePairing.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicPlaceProjection

theorem balanced_real_matrix {I : Type} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) (S : Matrix I I ℝ)
    (h : ∀ x y : I → ℝ, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z (S.mulVec x) y = AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z x (S.mulVec y)) :
    Z * S.map Complex.ofRealHom = (S.map Complex.ofRealHom)ᵀ * Z := by
  have hc (x : I → ℝ) : (fun i => (S.mulVec x i : ℂ)) =
      (S.map Complex.ofRealHom).mulVec (fun i => (x i : ℂ)) := by
    funext i
    exact Complex.ofRealHom.map_mulVec S x i
  have he (x y : I → ℝ) :
      (fun i => (x i : ℂ)) ⬝ᵥ (Z * S.map Complex.ofRealHom).mulVec (fun i => (y i : ℂ)) =
      (fun i => (x i : ℂ)) ⬝ᵥ ((S.map Complex.ofRealHom)ᵀ * Z).mulVec (fun i => (y i : ℂ)) := by
    have hh := h x y
    rw [← IntrinsicLocalJacobiPhase.Intrinsic.siegel_form_mulVec,← IntrinsicLocalJacobiPhase.Intrinsic.siegel_form_mulVec] at hh
    change (fun i => (S.mulVec x i : ℂ)) ⬝ᵥ Z.mulVec (fun i => (y i : ℂ)) =
      (fun i => (x i : ℂ)) ⬝ᵥ Z.mulVec (fun i => (S.mulVec y i : ℂ)) at hh
    rw [hc,hc,dotProduct_comm ((S.map Complex.ofRealHom).mulVec _),
      ← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec] at hh
    exact hh.symm
  have hsingle (i : I) : (fun j => ((Pi.single i 1 : I → ℝ) j : ℂ)) = Pi.single i 1 := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  ext i j
  have hh := he (Pi.single i 1) (Pi.single j 1)
  rw [hsingle,hsingle,single_dotProduct,single_dotProduct,one_mul,one_mul,
    Matrix.mulVec_single,Matrix.mulVec_single] at hh
  simp only [MulOpposite.op_one,one_smul] at hh
  exact hh

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}

theorem native_period_projection (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
    (v : Fin A.places) (z : Adelic.BallNatural.Ball) :
    (B.period z).matrix * IntrinsicFrameOn.IntrinsicPlaceProjection.positionPlaceMatrix B v = (IntrinsicFrameOn.IntrinsicPlaceProjection.positionPlaceMatrix B v)ᵀ * (B.period z).matrix := by
  apply balanced_real_matrix
  intro x y
  have hx : (LinearMap.toMatrix' (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v)).mulVec x =
      B.realPosition (Pi.single v (B.realPosition.symm x v)) := LinearMap.toMatrix'_mulVec _ x
  have hy : (LinearMap.toMatrix' (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v)).mulVec y =
      B.realPosition (Pi.single v (B.realPosition.symm y v)) := LinearMap.toMatrix'_mulVec _ y
  rw [hx,hy]
  have he := IntrinsicPlacePairing.Intrinsic.native_period_place_balance B hO z v (B.realPosition.symm x) (B.realPosition.symm y)
  rw [B.realPosition.apply_symm_apply,B.realPosition.apply_symm_apply] at he
  exact he

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPeriodProjection.Intrinsic
