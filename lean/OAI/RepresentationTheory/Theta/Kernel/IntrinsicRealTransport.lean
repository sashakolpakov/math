import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport

/-! # Intrinsic Real Transport -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealTransport.Intrinsic

noncomputable section

/-! The real phase change is built from the same native coordinate maps.
Its agreement with the rational phase change is proved on every rational
vector, using the complete native coordinate identifications. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicFrames OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic

def archPhaseSplit {V : Type} [Fintype V] :
    (V → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) ≃ₗ[ℝ] ((V → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 3) × (V → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 3)) where
  toFun x := (fun v => (IntrinsicSplitting.IntrinsicFrames.phaseSplit (x v)).1, fun v => (IntrinsicSplitting.IntrinsicFrames.phaseSplit (x v)).2)
  invFun x v := IntrinsicSplitting.IntrinsicFrames.phaseSplit.symm (x.1 v, x.2 v)
  left_inv x := by funext v; exact IntrinsicSplitting.IntrinsicFrames.phaseSplit.symm_apply_apply (x v)
  right_inv x := by
    apply Prod.ext <;> funext v
    · exact congrArg Prod.fst (IntrinsicSplitting.IntrinsicFrames.phaseSplit.apply_symm_apply (x.1 v, x.2 v))
    · exact congrArg Prod.snd (IntrinsicSplitting.IntrinsicFrames.phaseSplit.apply_symm_apply (x.1 v, x.2 v))
  map_add' x y := by
    apply Prod.ext <;> funext v
    · exact congrArg Prod.fst (IntrinsicSplitting.IntrinsicFrames.phaseSplit.map_add (x v) (y v))
    · exact congrArg Prod.snd (IntrinsicSplitting.IntrinsicFrames.phaseSplit.map_add (x v) (y v))
  map_smul' c x := by
    apply Prod.ext <;> funext v
    · exact congrArg Prod.fst (IntrinsicSplitting.IntrinsicFrames.phaseSplit.map_smul c (x v))
    · exact congrArg Prod.snd (IntrinsicSplitting.IntrinsicFrames.phaseSplit.map_smul c (x v))

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

def splitRealPhase : (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6) ≃L[ℝ]
    (((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) ⊕
      (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))) → ℝ) :=
  archPhaseSplit.toContinuousLinearEquiv.trans
    ((B₁.realPhase.prodCongr B₂.realPhase).trans IntrinsicPhaseTransport.Intrinsic.joinPhase.toContinuousLinearEquiv)

def realPhaseChange : ((Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕
    Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℝ) ≃L[ℝ]
    (((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) ⊕
      (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))) → ℝ) :=
  B.realPhase.symm.trans (splitRealPhase B₁ B₂)

variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form)}

theorem splitRealPhase_rational (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F 6) :
    splitRealPhase B₁ B₂
      (fun v j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j))) =
        fun i => (IntrinsicPhaseTransport.Intrinsic.splitRationalPhase B₁ B₂ x i : ℝ) := by
  have ha (v : Fin A.places) :
      (IntrinsicSplitting.IntrinsicFrames.phaseSplit (fun j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j)))).1 =
        fun j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) ((IntrinsicSplitting.IntrinsicFrames.phaseSplit x).1 j)) := by
    funext j
    rcases j with j | j <;> rfl
  have hb (v : Fin A.places) :
      (IntrinsicSplitting.IntrinsicFrames.phaseSplit (fun j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j)))).2 =
        fun j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) ((IntrinsicSplitting.IntrinsicFrames.phaseSplit x).2 j)) := by
    funext j
    rcases j with j | j <;> rfl
  have hleft : B₁.realPhase
      (fun v => (IntrinsicSplitting.IntrinsicFrames.phaseSplit (fun j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j)))).1) =
        fun i => (B₁.rationalPhase (IntrinsicSplitting.IntrinsicFrames.phaseSplit x).1 i : ℝ) := by
    simp_rw [ha]
    ext i
    exact h₁.2.2.2.1 (IntrinsicSplitting.IntrinsicFrames.phaseSplit x).1 i
  have hright : B₂.realPhase
      (fun v => (IntrinsicSplitting.IntrinsicFrames.phaseSplit (fun j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j)))).2) =
        fun i => (B₂.rationalPhase (IntrinsicSplitting.IntrinsicFrames.phaseSplit x).2 i : ℝ) := by
    simp_rw [hb]
    ext i
    exact h₂.2.2.2.1 (IntrinsicSplitting.IntrinsicFrames.phaseSplit x).2 i
  change IntrinsicPhaseTransport.Intrinsic.joinPhase
    (B₁.realPhase (fun v =>
      (IntrinsicSplitting.IntrinsicFrames.phaseSplit (fun j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j)))).1),
     B₂.realPhase (fun v =>
      (IntrinsicSplitting.IntrinsicFrames.phaseSplit (fun j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j)))).2)) = _
  rw [hleft, hright]
  funext i
  rcases i with i | i <;> cases i <;> rfl

theorem realPhaseChange_rational (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂) (hB : Adelic.DataTheta.CoordinateIdentification B P)
    (x : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℚ) :
    realPhaseChange B₁ B₂ B (fun i => (x i : ℝ)) =
      fun i => (IntrinsicPhaseTransport.Intrinsic.rationalPhaseChange B₁ B₂ B x i : ℝ) := by
  have hnative : B.realPhase
      (fun v j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v))
        (B.rationalPhase.symm x j))) = fun i => (x i : ℝ) := by
    ext i
    rw [hB.2.2.2.1, LinearEquiv.apply_symm_apply]
  change splitRealPhase B₁ B₂ (B.realPhase.symm (fun i => (x i : ℝ))) = _
  rw [← hnative, ContinuousLinearEquiv.symm_apply_apply,
    splitRealPhase_rational B₁ B₂ h₁ h₂]
  rfl

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealTransport.Intrinsic
