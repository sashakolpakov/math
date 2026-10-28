import OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealTransport
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorComponents

/-! # Intrinsic Coordinate Agreement -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.Intrinsic

/-! The rational, real, and complex transports are the same coordinate
change. The real/complex comparison uses the actual local symplectic
frames, their orthogonal sum, and the Hermitian real-tensor embedding. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicFrames OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorComponents.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : IntrinsicSplitting.IntrinsicSummands.SecondLine A)
variable (P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁) (P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form)

abbrev TotalRealTensor := ∀ v : Fin A.places,
  Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 2

def realCoordinates (s : TotalRealTensor A) : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 :=
  fun v j => A.real v (((IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂).localFrame (.inl (A.enumerate v))).coordinates (s v) j)

theorem realCoordinates_surjective : Function.Surjective (realCoordinates A S P₁ P₂) := by
  intro x
  let s : TotalRealTensor A := fun v =>
    (((IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂).localFrame (.inl (A.enumerate v))).coordinates).symm
      (fun j => (A.real v).symm (x v j))
  refine ⟨s,?_⟩
  funext v j
  change A.real v
    ((((IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂).localFrame (.inl (A.enumerate v))).coordinates)
      ((((IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂).localFrame (.inl (A.enumerate v))).coordinates).symm
        (fun j => (A.real v).symm (x v j))) j) = x v j
  rw [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem archPhaseSplit_realCoordinates (s : TotalRealTensor A) :
    IntrinsicRealTransport.Intrinsic.archPhaseSplit (realCoordinates A S P₁ P₂ s) =
      (fun v j => A.real v ((P₁.localFrame (.inl (A.enumerate v))).coordinates
        (fun q => s v (q.1,0)) j),
       fun v j => A.real v ((P₂.localFrame (.inl (A.enumerate v))).coordinates
        (fun q => s v (q.1,1)) j)) := by
  have he (v : Fin A.places) :
      IntrinsicSplitting.IntrinsicFrames.phaseSplit (((IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂).localFrame (.inl (A.enumerate v))).coordinates (s v)) =
        ((P₁.localFrame (.inl (A.enumerate v))).coordinates (fun q => s v (q.1,0)),
         (P₂.localFrame (.inl (A.enumerate v))).coordinates (fun q => s v (q.1,1))) := by
    change IntrinsicSplitting.IntrinsicFrames.phaseSplit (IntrinsicSplitting.IntrinsicFrames.phaseSplit.symm _) = _
    exact IntrinsicSplitting.IntrinsicFrames.phaseSplit.apply_symm_apply _
  apply Prod.ext
  · funext v j
    rcases j with j | j
    · exact congrArg (fun p => A.real v (p.1 (.inl j))) (he v)
    · exact congrArg (fun p => A.real v (p.1 (.inr j))) (he v)
  · funext v j
    rcases j with j | j
    · exact congrArg (fun p => A.real v (p.2 (.inl j))) (he v)
    · exact congrArg (fun p => A.real v (p.2 (.inr j))) (he v)

variable {A S P₁ P₂}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

theorem complexPhaseChange_realTensor (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hB : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂)) (s : TotalRealTensor A) :
    IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B
      (fun i => (B.realPhase (realCoordinates A S P₁ P₂ s) i : ℂ)) =
        fun i => (IntrinsicRealTransport.Intrinsic.splitRealPhase B₁ B₂ (realCoordinates A S P₁ P₂ s) i : ℂ) := by
  have hgeo : B.complexPhase (fun i => (B.realPhase (realCoordinates A S P₁ P₂ s) i : ℂ)) =
      Adelic.BallGeometryData.realTensorComponents (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) s := hB.2.2.2.2.2.2.1 s
  change IntrinsicPhaseTransport.Intrinsic.joinPhase
    (B₁.complexPhase.symm ((IntrinsicComplexTransport.Intrinsic.geometricSplit A S (B.complexPhase
      (fun i => (B.realPhase (realCoordinates A S P₁ P₂ s) i : ℂ)))).1),
     B₂.complexPhase.symm ((IntrinsicComplexTransport.Intrinsic.geometricSplit A S (B.complexPhase
      (fun i => (B.realPhase (realCoordinates A S P₁ P₂ s) i : ℂ)))).2)) = _
  rw [hgeo, IntrinsicTensorComponents.Intrinsic.geometricSplit_realTensor]
  dsimp only [Prod.fst, Prod.snd]
  rw [← h₁.2.2.2.2.2.2.1 (fun v q => s v (q.1,0)),
    ← h₂.2.2.2.2.2.2.1 (fun v q => s v (q.1,1)),
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  change IntrinsicPhaseTransport.Intrinsic.joinPhase _ = fun i =>
    ((IntrinsicPhaseTransport.Intrinsic.joinPhase (k := ℝ) (B₁.realPhase (IntrinsicRealTransport.Intrinsic.archPhaseSplit (realCoordinates A S P₁ P₂ s)).1,
      B₂.realPhase (IntrinsicRealTransport.Intrinsic.archPhaseSplit (realCoordinates A S P₁ P₂ s)).2) i : ℝ) : ℂ)
  rw [archPhaseSplit_realCoordinates]
  funext i
  rcases i with i | i <;> cases i <;> rfl

theorem complexPhaseChange_real (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hB : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (x : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℝ) :
    IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B (fun i => (x i : ℂ)) =
      fun i => (IntrinsicRealTransport.Intrinsic.realPhaseChange B₁ B₂ B x i : ℂ) := by
  obtain ⟨s,hs⟩ := realCoordinates_surjective A S P₁ P₂ (B.realPhase.symm x)
  have he : x = B.realPhase (realCoordinates A S P₁ P₂ s) := by
    rw [hs, ContinuousLinearEquiv.apply_symm_apply]
  rw [he]
  change IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B _ = fun i =>
    (IntrinsicRealTransport.Intrinsic.splitRealPhase B₁ B₂ (B.realPhase.symm (B.realPhase (realCoordinates A S P₁ P₂ s))) i : ℂ)
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact complexPhaseChange_realTensor B₁ B₂ B h₁ h₂ hB s

theorem complexPhaseChange_rational (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hB : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (x : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℚ) :
    IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B (fun i => (x i : ℂ)) =
      fun i => (IntrinsicPhaseTransport.Intrinsic.rationalPhaseChange B₁ B₂ B x i : ℂ) := by
  have h := complexPhaseChange_real B₁ B₂ B h₁ h₂ hB (fun i => (x i : ℝ))
  rw [IntrinsicRealTransport.Intrinsic.realPhaseChange_rational B₁ B₂ B h₁ h₂ hB] at h
  simpa only [Complex.ofReal_ratCast] using h

end RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport

/-! The complex coordinate change preserves the position polarization.
This is derived from its rational agreement; no block or slot compatibility
is assumed for the native total comparison data. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.Intrinsic

theorem complexLinear_ext_rational {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (f g : (I → ℂ) →ₗ[ℂ] (J → ℂ))
    (h : ∀ x : I → ℚ, f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) : f = g := by
  apply LinearMap.toMatrix'.injective
  ext i j
  have hc : (fun k : I => ((Pi.single j (1 : ℚ) : I → ℚ) k : ℂ)) =
      (Pi.single j (1 : ℂ) : I → ℂ) := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  have he := h (Pi.single j 1)
  rw [hc] at he
  exact congrFun he i

def positions (k I : Type) [Field k] : ((I ⊕ I) → k) →ₗ[k] (I → k) where
  toFun x i := x (.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def embedPosition (k I : Type) [Field k] : (I → k) →ₗ[k] ((I ⊕ I) → k) where
  toFun x := Sum.elim x 0
  map_add' _ _ := by funext i; cases i <;> simp
  map_smul' _ _ := by funext i; cases i <;> simp

def embedMomentum (k I : Type) [Field k] : (I → k) →ₗ[k] ((I ⊕ I) → k) where
  toFun x := Sum.elim 0 x
  map_add' _ _ := by funext i; cases i <;> simp
  map_smul' _ _ := by funext i; cases i <;> simp

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

def complexPositionChange : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) →ₗ[ℂ]
    ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) → ℂ) :=
  (positions ℂ _).comp ((IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B).toLinearMap.comp (embedPosition ℂ _))

theorem complexPhaseChange_momentum (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hB : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂)) :
    (positions ℂ _).comp ((IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B).toLinearMap.comp
      (embedMomentum ℂ _)) = 0 := by
  apply complexLinear_ext_rational
  intro x
  have he := Intrinsic.complexPhaseChange_rational B₁ B₂ B h₁ h₂ hB
    (Sum.elim (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ) x)
  have hp (i : Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) :=
    IntrinsicPhaseTransport.Intrinsic.rationalPhaseChange_position B₁ B₂ B h₁ h₂ hB
      (Sum.elim (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ) x) i
  ext i
  have hi := congrFun he (.inl i)
  rw [hp] at hi
  change IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B
    (fun j => ((Sum.elim (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ) x) j : ℂ)) (.inl i) =
      (IntrinsicPhaseTransport.Intrinsic.rationalPositionChange B₁ B₂ B (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ) i : ℂ) at hi
  rw [map_zero] at hi
  have hc : (fun j => ((Sum.elim (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ) x) j : ℂ)) =
      Sum.elim (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) (fun j => (x j : ℂ)) := by
    funext j
    cases j <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Rat.cast_zero]
  rw [hc] at hi
  change IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B
    (Sum.elim (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) (fun j => (x j : ℂ))) (.inl i) = 0
  simpa only [Pi.zero_apply, Rat.cast_zero] using hi

theorem complexPhaseChange_positions (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hB : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (x : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℂ) :
    positions ℂ _ (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B x) =
      complexPositionChange B₁ B₂ B (positions ℂ _ x) := by
  have hx : x = embedPosition ℂ _ (positions ℂ _ x) +
      embedMomentum ℂ _ (fun i => x (.inr i)) := by
    funext i
    cases i <;> simp [embedPosition, embedMomentum, positions]
  have hm := congrArg (fun f => f (fun i => x (.inr i)))
    (complexPhaseChange_momentum B₁ B₂ B h₁ h₂ hB)
  change positions ℂ _ (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B (embedMomentum ℂ _ (fun i => x (.inr i)))) = 0 at hm
  calc
    positions ℂ _ (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B x) =
        positions ℂ _ (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B
          (embedPosition ℂ _ (positions ℂ _ x) + embedMomentum ℂ _ (fun i => x (.inr i)))) :=
      congrArg (fun y => positions ℂ _ (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B y)) hx
    _ = _ := by rw [map_add, map_add, hm, add_zero]; rfl

end RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport

end

end OAI
