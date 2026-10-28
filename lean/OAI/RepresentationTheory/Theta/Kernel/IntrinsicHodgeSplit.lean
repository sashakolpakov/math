import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameEntries

/-! # Intrinsic Hodge Split -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit.Intrinsic

noncomputable section

/-! The literal splitting of the Hodge frame and its multiplicity slots
for the constructed orthogonal sum. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameEntries.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : IntrinsicSplitting.IntrinsicSummands.SecondLine A)

def frameIndex : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ≃
    (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) where
  toFun q := if q.2.2 = 0 then .inl (q.1, q.2.1, 0) else .inr (q.1, q.2.1, 0)
  invFun := Sum.elim (fun q => (q.1, q.2.1, 0)) (fun q => (q.1, q.2.1, 1))
  left_inv q := by rcases q with ⟨v,i,r⟩; fin_cases r <;> rfl
  right_inv q := by
    rcases q with ⟨v,i,r⟩ | ⟨v,i,r⟩ <;> fin_cases r <;> rfl

theorem frameIndex_symm_left (q : Adelic.BallGeometryData.FrameIndex A) :
    (frameIndex A S).symm (.inl q) = (q.1, q.2.1, 0) := rfl

theorem frameIndex_symm_right (q : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) :
    (frameIndex A S).symm (.inr q) = (q.1, q.2.1, 1) := rfl

def splitCoordinates : (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) ≃L[ℂ]
    ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) → ℂ) :=
  (ContinuousLinearEquiv.piCongrLeft ℂ
    (fun _ : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) => ℂ) (frameIndex A S).symm).symm

theorem splitCoordinates_left (x : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) (q : Adelic.BallGeometryData.FrameIndex A) :
    splitCoordinates A S x (.inl q) = x (q.1, q.2.1, 0) := rfl

theorem splitCoordinates_right (x : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ)
    (q : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) :
    splitCoordinates A S x (.inr q) = x (q.1, q.2.1, 1) := rfl

theorem split_slot_left (u : Fin 2 → ℂ) :
    splitCoordinates A S (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 0 u) =
      Sum.elim (OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := A) u) (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) := by
  funext q
  rcases q with q | q
  · change IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 0 u
      (q.1, q.2.1, 0) = OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := A) u q
    rcases q with ⟨v,i,r⟩
    fin_cases r
    rw [IntrinsicFrameEntries.Intrinsic.second_slot_apply, IntrinsicFrameEntries.Intrinsic.first_slot_apply]
    simp [Prod.mk.injEq, IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic]
  · change IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 0 u
      (q.1, q.2.1, 1) = 0
    rw [IntrinsicFrameEntries.Intrinsic.second_slot_apply]
    simp [Prod.mk.injEq]

theorem split_slot_right (u : Fin 2 → ℂ) :
    splitCoordinates A S (IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 1 u) =
      Sum.elim (0 : Adelic.BallGeometryData.FrameIndex A → ℂ)
        (OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) u) := by
  funext q
  rcases q with q | q
  · change IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 1 u
      (q.1, q.2.1, 0) = 0
    rw [IntrinsicFrameEntries.Intrinsic.second_slot_apply]
    simp [Prod.mk.injEq]
  · change IntrinsicSecondProjection.Intrinsic.slotEmbedding (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 1 u
      (q.1, q.2.1, 1) = OneFormsIntrinsicLattice.IntrinsicProjection.slotEmbedding (A := IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) u q
    rcases q with ⟨v,i,r⟩
    fin_cases r
    rw [IntrinsicFrameEntries.Intrinsic.second_slot_apply, IntrinsicFrameEntries.Intrinsic.first_slot_apply]
    simp [Prod.mk.injEq, IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic, IntrinsicSplitting.IntrinsicSummands.secondArithmetic]

theorem frameMatrix_blocks (g : Adelic.RationalSU.ArchimedeanSU F H) (z : Adelic.BallNatural.Ball) :
    (Adelic.BallGeometryData.frameMatrix (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) g z).submatrix
      (frameIndex A S).symm (frameIndex A S).symm =
    Matrix.fromBlocks (Adelic.BallGeometryData.frameMatrix A g z) 0 0 (Adelic.BallGeometryData.frameMatrix (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) g z) := by
  apply Matrix.ext
  intro p q
  rcases p with p | p <;> rcases q with q | q
  · change Adelic.BallGeometryData.frameMatrix (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) g z (p.1,p.2.1,0) (q.1,q.2.1,0) =
      Adelic.BallGeometryData.frameMatrix A g z p q
    rcases p with ⟨v,i,r⟩
    rcases q with ⟨w,j,s⟩
    fin_cases r
    fin_cases s
    rw [IntrinsicFrameEntries.Intrinsic.frameMatrix_entry, IntrinsicFrameEntries.Intrinsic.frameMatrix_entry]
    simp only [eq_self, and_true]
    by_cases hv : v = w <;> simp [hv, IntrinsicFrameEntries.Intrinsic.frameCoefficient, Adelic.BallGeometryData.standardMatrix]
  · change Adelic.BallGeometryData.frameMatrix (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) g z (p.1,p.2.1,0) (q.1,q.2.1,1) = 0
    rw [IntrinsicFrameEntries.Intrinsic.frameMatrix_entry]
    simp
  · change Adelic.BallGeometryData.frameMatrix (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) g z (p.1,p.2.1,1) (q.1,q.2.1,0) = 0
    rw [IntrinsicFrameEntries.Intrinsic.frameMatrix_entry]
    simp
  · change Adelic.BallGeometryData.frameMatrix (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) g z (p.1,p.2.1,1) (q.1,q.2.1,1) =
      Adelic.BallGeometryData.frameMatrix (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) g z p q
    rcases p with ⟨v,i,r⟩
    rcases q with ⟨w,j,s⟩
    fin_cases r
    fin_cases s
    rw [IntrinsicFrameEntries.Intrinsic.frameMatrix_entry, IntrinsicFrameEntries.Intrinsic.frameMatrix_entry]
    simp only [eq_self, and_true]
    by_cases hv : v = w <;> simp [hv, IntrinsicFrameEntries.Intrinsic.frameCoefficient, Adelic.BallGeometryData.standardMatrix]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit.Intrinsic
