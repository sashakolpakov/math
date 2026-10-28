import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceCotangent
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumProjection
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualEquiv

/-! # Intrinsic Local Residual Equiv -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualEquiv.IntrinsicLocality

/-! The actual residual symplectic equivalence is local at each
archimedean place. Locality follows from native Gaussian orthogonality
and the geometric graph, without assuming aligned coordinate gauges. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceCotangent.IntrinsicReal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualEquiv.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}

theorem cotangent_place_projection (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball)
    (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v (IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B u) =
      IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B (Pi.single v (u v)) := by
  have hlocal (side : Fin 6 → Fin 6 ⊕ Fin 6) :
      (fun w j => (Pi.single v (u v) : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) w (side j)) =
        Pi.single v (fun j => u v (side j)) := by
    funext w j
    by_cases hw : w = v
    · subst w
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne hw,Pi.zero_apply]
  rw [IntrinsicPlaceCotangent.IntrinsicReal.native_real_place_cotangent B hC hG hO v z]
  funext i
  cases i with
  | inl i =>
    change B.realPosition (Pi.single v (B.realPosition.symm (B.realPosition (fun w j => u w (.inl j))) v)) i =
      B.realPosition (fun w j => (Pi.single v (u v) : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) w (.inl j)) i
    rw [B.realPosition.symm_apply_apply,hlocal Sum.inl]
  | inr i =>
    change (LinearMap.toMatrix' (IntrinsicPositionProjection.Intrinsic.realPositionProjection B v))ᵀ.mulVec
      (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun w j => u w (.inr j))) i =
        IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B (fun w j => (Pi.single v (u v) : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) w (.inr j)) i
    rw [IntrinsicMomentumProjection.Intrinsic.momentum_place_projection,hlocal Sum.inr]

theorem residual_place_projection (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball)
    (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B (Pi.single v (u v)) = Pi.single v (IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B u v) := by
  apply B.realPhase.injective
  change B.realPhase (B.realPhase.symm (IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B (Pi.single v (u v)))) =
    IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v (IntrinsicCotangentAction.Intrinsic.cotangentCoordinates B u)
  rw [B.realPhase.apply_symm_apply]
  exact (cotangent_place_projection B hC hG hO v z u).symm

theorem residual_inverse_place_projection (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball)
    (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    (IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B).symm (Pi.single v (u v)) =
      Pi.single v ((IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B).symm u v) := by
  apply (IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,residual_place_projection B hC hG hO v z,
    ContinuousLinearEquiv.apply_symm_apply]

end RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualEquiv.IntrinsicLocality

namespace RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualEquiv.Intrinsic

/-! Restriction of the actual residual symplectic equivalence to one
archimedean place, with its actual inverse and local pairing identity. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualEquiv.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualEquiv.IntrinsicLocality

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}

def localResidualLinearEquiv (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball) :
    Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 ≃ₗ[ℝ] Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 where
  toFun x := IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B (Pi.single v x) v
  invFun x := (IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B).symm (Pi.single v x) v
  left_inv x := by
    simp only [IntrinsicLocality.residual_inverse_place_projection B hC hG hO v z,
      ContinuousLinearEquiv.symm_apply_apply,Pi.single_eq_same]
  right_inv x := by
    simp only [IntrinsicLocality.residual_place_projection B hC hG hO v z,
      ContinuousLinearEquiv.apply_symm_apply,Pi.single_eq_same]
  map_add' x y := by
    rw [Pi.single_add,map_add]
    rfl
  map_smul' c x := by
    rw [Pi.single_smul,map_smul]
    rfl

def localResidualContinuousEquiv (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball) :
    Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 ≃L[ℝ] Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 :=
  (localResidualLinearEquiv B hC hG hO v z).toContinuousLinearEquiv

theorem local_residual_apply (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball)
    (u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    localResidualContinuousEquiv B hC hG hO v z (u v) = IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B u v := by
  exact (congrFun (IntrinsicLocality.residual_place_projection B hC hG hO v z u) v).trans (Pi.single_eq_same v _)

theorem local_residual_pairing (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D) (v : Fin A.places) (z : Adelic.BallNatural.Ball)
    (x y : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    Adelic.DataTheta.standardPairing (localResidualContinuousEquiv B hC hG hO v z x)
      (localResidualContinuousEquiv B hC hG hO v z y) = Adelic.DataTheta.standardPairing x y := by
  have hs (a b : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
      (∑ w : Fin A.places, Adelic.DataTheta.standardPairing ((Pi.single v a : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) w)
        ((Pi.single v b : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) w)) = Adelic.DataTheta.standardPairing a b := by
    rw [Finset.sum_eq_single v]
    · rw [Pi.single_eq_same,Pi.single_eq_same]
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw,Adelic.DataTheta.standardPairing]
    · simp
  have hsingle (a : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) : IntrinsicResidualEquiv.Intrinsic.residualContinuousEquiv B (Pi.single v a) =
      Pi.single v (localResidualContinuousEquiv B hC hG hO v z a) := by
    have he := IntrinsicLocality.residual_place_projection B hC hG hO v z (Pi.single v a)
    simp only [Pi.single_eq_same] at he
    exact he
  have he := IntrinsicResidualEquiv.Intrinsic.residual_equiv_pairing B hC (Pi.single v x) (Pi.single v y)
  rw [hsingle,hsingle,hs,hs] at he
  exact he

end RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualEquiv.Intrinsic

end

end OAI
