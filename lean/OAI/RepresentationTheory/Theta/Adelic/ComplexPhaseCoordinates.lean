import OAI.RepresentationTheory.Theta.Adelic.RealTensorCoordinates
import OAI.RepresentationTheory.Theta.Adelic.ComplexLinearExtension

/-! # Complex Phase Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates

noncomputable section

/-! The complex coordinate identification is the complexification of
the actual trace tensor space, with the prescribed Hermitian dual signs. -/

open scoped Classical _root_.NumberField Kronecker ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates
open OAI.RepresentationTheory.Theta.Adelic.RealTensorCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexLinearExtension.PairedComplexification

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def flatRealTensorLinearEquiv :
    ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) ≃ₗ[ℝ] (BallGeometryData.FrameIndex A → ℂ) :=
  (RealTensorCoordinates.totalRealTensorEquiv A P).toLinearEquiv.trans
    ((LinearEquiv.curry ℂ ℂ (Fin A.places) (Fin 3 × Fin m)).symm.restrictScalars ℝ)

def tensorDualSign (i : BallGeometryData.FrameIndex A) : ℂ :=
  (if i.1 = A.distinguished ∧ i.2.1 = 2 then (-1 : ℂ) else 1) *
    (if A.positive i.1 i.2.2 then (1 : ℂ) else -1)

theorem tensorDualSign_mul_self (i : BallGeometryData.FrameIndex A) :
    tensorDualSign A i * tensorDualSign A i = 1 := by
  dsimp [tensorDualSign]
  split_ifs <;> norm_num

def pairedTensorEquiv : ((BallGeometryData.FrameIndex A → ℂ) × (BallGeometryData.FrameIndex A → ℂ)) ≃ₗ[ℂ] BallGeometryData.ComplexPhase A where
  toFun w v := (fun ij => w.1 (v, ij), fun ij => tensorDualSign A (v, ij) * w.2 (v, ij))
  invFun w := (fun i => (w i.1).1 i.2, fun i => tensorDualSign A i * (w i.1).2 i.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext i
      change tensorDualSign A i * (tensorDualSign A i * w.2 i) = w.2 i
      rw [← mul_assoc, tensorDualSign_mul_self, one_mul]
  right_inv w := by
    funext v
    apply Prod.ext
    · rfl
    · funext ij
      change tensorDualSign A (v, ij) * (tensorDualSign A (v, ij) * (w v).2 ij) = _
      rw [← mul_assoc, tensorDualSign_mul_self, one_mul]
  map_add' x y := by
    funext v
    apply Prod.ext
    · rfl
    · funext ij; exact mul_add _ _ _
  map_smul' c x := by
    funext v
    apply Prod.ext
    · rfl
    · funext ij; exact mul_left_comm _ _ _

def complexPhaseCoordinates :
    ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) ≃L[ℂ] BallGeometryData.ComplexPhase A :=
  LinearEquiv.toContinuousLinearEquiv
    ((ComplexLinearExtension.PairedComplexification.pairedComplexEquiv (flatRealTensorLinearEquiv A P)).trans (pairedTensorEquiv A))

theorem flatRealTensorLinearEquiv_native
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    flatRealTensorLinearEquiv A P (PhaseCoordinates.realPhaseCoordinates A (fun v i => A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates (s v) i))) =
        fun i => ((A.basisV i.1).inv ⊗ₖ (A.basisP i.1).inv).mulVec
          (fun ij => A.complex i.1 (s i.1 ij)) i.2 := by
  funext i
  change RealTensorCoordinates.realTensorEquiv A P i.1
    (((PhaseCoordinates.realPhaseCoordinates A).symm (PhaseCoordinates.realPhaseCoordinates A
      (fun v j => A.real v ((P.localFrame (.inl (A.enumerate v))).coordinates (s v) j)))) i.1) i.2 = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact congrFun (RealTensorCoordinates.realTensorEquiv_native A P i.1 (s i.1)) i.2

theorem complexPhaseCoordinates_native
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    complexPhaseCoordinates A P (fun i => (PhaseCoordinates.realPhaseCoordinates A (fun v j => A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates (s v) j)) i : ℂ)) =
        BallGeometryData.realTensorComponents A s := by
  change pairedTensorEquiv A (ComplexLinearExtension.PairedComplexification.pairedComplexMap (flatRealTensorLinearEquiv A P)
    (fun i => (PhaseCoordinates.realPhaseCoordinates A (fun v j => A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates (s v) j)) i : ℂ))) = _
  rw [ComplexLinearExtension.PairedComplexification.pairedComplexMap_real, flatRealTensorLinearEquiv_native]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates
