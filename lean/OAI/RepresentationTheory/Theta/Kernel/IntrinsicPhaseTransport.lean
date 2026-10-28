import OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting

/-! # Intrinsic Phase Transport -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic

noncomputable section

/-! The rational phase change between the native total construction and
the two native summands. It is built from their actual coordinate maps;
trace-symplectic compatibility and preservation of positions are derived
from the complete coordinate identifications. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicFrames OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.IntrinsicKernel

def joinPhase {k I J : Type} [Field k] :
    (((I ⊕ I) → k) × ((J ⊕ J) → k)) ≃ₗ[k] (((I ⊕ J) ⊕ (I ⊕ J)) → k) where
  toFun p := Sum.elim
    (Sum.elim (fun i => p.1 (.inl i)) (fun j => p.2 (.inl j)))
    (Sum.elim (fun i => p.1 (.inr i)) (fun j => p.2 (.inr j)))
  invFun x :=
    (Sum.elim (fun i => x (.inl (.inl i))) (fun i => x (.inr (.inl i))),
     Sum.elim (fun j => x (.inl (.inr j))) (fun j => x (.inr (.inr j))))
  left_inv p := by apply Prod.ext <;> funext i <;> cases i <;> rfl
  right_inv x := by funext i; rcases i with i | i <;> cases i <;> rfl
  map_add' _ _ := by funext i; rcases i with i | i <;> cases i <;> rfl
  map_smul' _ _ := by funext i; rcases i with i | i <;> cases i <;> rfl

theorem joinPhase_pairing {k I J : Type} [Field k] [Fintype I] [Fintype J]
    (x y : ((I ⊕ I) → k) × ((J ⊕ J) → k)) :
    Adelic.DataTheta.standardPairing (joinPhase x) (joinPhase y) =
      Adelic.DataTheta.standardPairing x.1 y.1 + Adelic.DataTheta.standardPairing x.2 y.2 := by
  simp only [Adelic.DataTheta.standardPairing, Fintype.sum_sum_type, joinPhase, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr]

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

def splitRationalPhase : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F 6 ≃ₗ[ℚ]
    (((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) ⊕
      (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))) → ℚ) :=
  ((IntrinsicSplitting.IntrinsicFrames.phaseSplit (k := F)).restrictScalars ℚ).trans
    ((B₁.rationalPhase.prodCongr B₂.rationalPhase).trans joinPhase)

def rationalPhaseChange : ((Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕
    Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℚ) ≃ₗ[ℚ]
    (((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) ⊕
      (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))) → ℚ) :=
  B.rationalPhase.symm.trans (splitRationalPhase B₁ B₂)

def rationalPositionChange : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ) ≃ₗ[ℚ]
    ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) → ℚ) :=
  B.rationalPosition.symm.trans (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition)

variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form)}

theorem splitRationalPhase_position (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F 6)
    (i : Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) :
    splitRationalPhase B₁ B₂ x (.inl i) =
      IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition (fun j => x (.inl j)) i := by
  rcases i with i | i
  · change B₁.rationalPhase (IntrinsicSplitting.IntrinsicFrames.phaseSplit x).1 (.inl i) = _
    rw [h₁.2.1]
    rfl
  · change B₂.rationalPhase (IntrinsicSplitting.IntrinsicFrames.phaseSplit x).2 (.inl i) = _
    rw [h₂.2.1]
    rfl

theorem splitRationalPhase_pairing (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂) (x y : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F 6) :
    Adelic.DataTheta.standardPairing (splitRationalPhase B₁ B₂ x) (splitRationalPhase B₁ B₂ y) =
      Algebra.trace ℚ F (Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 2 x y) := by
  change Adelic.DataTheta.standardPairing
    (joinPhase (B₁.rationalPhase (IntrinsicSplitting.IntrinsicFrames.phaseSplit x).1, B₂.rationalPhase (IntrinsicSplitting.IntrinsicFrames.phaseSplit x).2))
    (joinPhase (B₁.rationalPhase (IntrinsicSplitting.IntrinsicFrames.phaseSplit y).1, B₂.rationalPhase (IntrinsicSplitting.IntrinsicFrames.phaseSplit y).2)) = _
  rw [joinPhase_pairing, h₁.2.2.1, h₂.2.2.1, IntrinsicSplitting.IntrinsicFrames.phaseSplit_pairing, map_add]

theorem rationalPhaseChange_pairing (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂) (hB : Adelic.DataTheta.CoordinateIdentification B P)
    (x y : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℚ) :
    Adelic.DataTheta.standardPairing (rationalPhaseChange B₁ B₂ B x) (rationalPhaseChange B₁ B₂ B y) =
      Adelic.DataTheta.standardPairing x y := by
  change Adelic.DataTheta.standardPairing (splitRationalPhase B₁ B₂ (B.rationalPhase.symm x))
    (splitRationalPhase B₁ B₂ (B.rationalPhase.symm y)) = _
  rw [splitRationalPhase_pairing B₁ B₂ h₁ h₂, ← hB.2.2.1]
  simp only [LinearEquiv.apply_symm_apply]

theorem rationalPhaseChange_position (h₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁)
    (h₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂) (hB : Adelic.DataTheta.CoordinateIdentification B P)
    (x : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℚ)
    (i : Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) :
    rationalPhaseChange B₁ B₂ B x (.inl i) =
      rationalPositionChange B₁ B₂ B (fun j => x (.inl j)) i := by
  change splitRationalPhase B₁ B₂ (B.rationalPhase.symm x) (.inl i) = _
  rw [splitRationalPhase_position B₁ B₂ h₁ h₂]
  have he : (fun j => B.rationalPhase.symm x (.inl j)) =
      B.rationalPosition.symm (fun j => x (.inl j)) := by
    apply B.rationalPosition.injective
    ext j
    rw [← hB.2.1, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [he]
  rfl

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic
