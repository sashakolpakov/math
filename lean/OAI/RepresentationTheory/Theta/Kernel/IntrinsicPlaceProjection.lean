import OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealComplexification
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne

/-! # Intrinsic Place Projection -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection.Intrinsic

noncomputable section

/-! Projection to an archimedean place in arbitrary full native
comparison coordinates. The locality comes from the actual tensor and
local symplectic frames in CoordinateIdentification. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicCoordinateAgreement
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealComplexification.Intrinsic

def placeProjection {R V W : Type} [Semiring R] [Fintype V] [DecidableEq V]
    [AddCommMonoid W] [Module R W] (v : V) : (V → W) →ₗ[R] (V → W) :=
  (LinearMap.single R (fun _ : V => W) v).comp (LinearMap.proj v)

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

def geometricPlaceProjection (v : Fin A.places) : Adelic.BallGeometryData.ComplexPhase A →ₗ[ℂ] Adelic.BallGeometryData.ComplexPhase A :=
  placeProjection v

def nativeRealTensor (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K) (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    ∀ v : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 2 :=
  fun v => ((P.localFrame (.inl (A.enumerate v))).coordinates).symm
    (fun j => (A.real v).symm (x v j))

theorem nativeRealTensor_single (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K) (v : Fin A.places)
    (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) :
    nativeRealTensor A P (Pi.single v (x v)) = Pi.single v (nativeRealTensor A P x v) := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [nativeRealTensor]
  · simp [nativeRealTensor,hw]
    rfl

theorem geometric_native_projection (v : Fin A.places)
    (s : ∀ w : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate w)) d) 3 2) :
    geometricPlaceProjection A v (Adelic.BallGeometryData.realTensorComponents A s) =
      Adelic.BallGeometryData.realTensorComponents A (Pi.single v (s v)) := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [geometricPlaceProjection,placeProjection,Adelic.BallGeometryData.realTensorComponents]
  · apply Prod.ext <;> funext ij <;>
      simp [geometricPlaceProjection,placeProjection,Adelic.BallGeometryData.realTensorComponents,hw,Matrix.mulVec,dotProduct]

variable {A}
variable (B : Adelic.DataTheta.ComparisonData F H K A)

def realPlaceProjection (v : Fin A.places) :
    ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) →ₗ[ℝ] ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) :=
  B.realPhase.toLinearMap.comp ((placeProjection (R := ℝ) v).comp B.realPhase.symm.toLinearMap)

theorem complex_place_projection {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (v : Fin A.places) (u : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℂ) :
    B.complexPhase (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (realPlaceProjection B v) u) =
      geometricPlaceProjection A v (B.complexPhase u) := by
  have hlinear : B.complexPhase.toLinearMap.comp (IntrinsicRealComplexification.Intrinsic.complexifiedLinear (realPlaceProjection B v)) =
      (geometricPlaceProjection A v).comp B.complexPhase.toLinearMap := by
    apply IntrinsicRealComplexification.Intrinsic.complexLinear_ext_real
    intro y
    let x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 := B.realPhase.symm y
    have hB : B.complexPhase (fun i => (y i : ℂ)) = Adelic.BallGeometryData.realTensorComponents A (nativeRealTensor A P x) :=
      (congrArg (fun t => B.complexPhase (fun i => (t i : ℂ))) (B.realPhase.apply_symm_apply y)).symm.trans
        (IntrinsicCompactOne.IntrinsicCoordinateAgreement.comparison_real_components B hC x)
    have hnew := IntrinsicCompactOne.IntrinsicCoordinateAgreement.comparison_real_components B hC (Pi.single v (x v))
    have hc := congrArg B.complexPhase (IntrinsicRealComplexification.Intrinsic.complexifiedLinear_real (realPlaceProjection B v) y)
    exact hc.trans (hnew.trans
      ((congrArg (Adelic.BallGeometryData.realTensorComponents A) (nativeRealTensor_single A P v x)).trans
        ((geometric_native_projection A v (nativeRealTensor A P x)).symm.trans
          (congrArg (geometricPlaceProjection A v) hB.symm))))
  exact LinearMap.congr_fun hlinear u

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection.Intrinsic
