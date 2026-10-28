import OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport

/-! # Intrinsic Complex Transport -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic

noncomputable section

/-! Actual complex Hodge-coordinate transport. The graph identity follows
from the three complete native geometry identifications and the literal
splitting of the multiplicity-two Hodge frame. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : IntrinsicSplitting.IntrinsicSummands.SecondLine A)

def geometricSplit : Adelic.BallGeometryData.ComplexPhase (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ≃ₗ[ℂ]
    (Adelic.BallGeometryData.ComplexPhase A × Adelic.BallGeometryData.ComplexPhase (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) where
  toFun x :=
    (fun v => (fun q => (x v).1 (q.1,0), fun q => (x v).2 (q.1,0)),
     fun v => (fun q => (x v).1 (q.1,1), fun q => (x v).2 (q.1,1)))
  invFun x v :=
    (fun q => if q.2 = 0 then (x.1 v).1 (q.1,0) else (x.2 v).1 (q.1,0),
     fun q => if q.2 = 0 then (x.1 v).2 (q.1,0) else (x.2 v).2 (q.1,0))
  left_inv x := by
    funext v
    apply Prod.ext <;> funext q <;> rcases q with ⟨i,r⟩ <;> fin_cases r <;> rfl
  right_inv x := by
    apply Prod.ext <;> funext v <;> apply Prod.ext <;> funext q
    all_goals rcases q with ⟨i,r⟩; fin_cases r; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem geometricSplit_frame (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    geometricSplit A S (Adelic.BallGeometryData.geometricFrame (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) z a) =
      (Adelic.BallGeometryData.geometricFrame A z (fun q => a (q.1,q.2.1,0)),
       Adelic.BallGeometryData.geometricFrame (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) z (fun q => a (q.1,q.2.1,1))) := by
  apply Prod.ext <;> funext v <;> apply Prod.ext <;> funext q
  all_goals
    rcases q with ⟨i,r⟩
    fin_cases r
    rfl

theorem joinPhase_graph {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J)
    (a : (Matrix I I ℂ)ˣ) (b : (Matrix J J ℂ)ˣ) (u : I → ℂ) (v : J → ℂ) :
    IntrinsicPhaseTransport.Intrinsic.joinPhase (Sum.elim (a.val.mulVec u) (Z₁.matrix.mulVec (a.val.mulVec u)),
      Sum.elim (b.val.mulVec v) (Z₂.matrix.mulVec (b.val.mulVec v))) =
      Sum.elim ((IntrinsicBlockSiegel.Intrinsic.blockFrame a b).val.mulVec (Sum.elim u v))
        ((IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂).matrix.mulVec ((IntrinsicBlockSiegel.Intrinsic.blockFrame a b).val.mulVec (Sum.elim u v))) := by
  funext i
  rcases i with i | i <;> rcases i with i | i
  all_goals simp [IntrinsicPhaseTransport.Intrinsic.joinPhase, IntrinsicBlockSiegel.Intrinsic.blockFrame, IntrinsicBlockSiegel.Intrinsic.blockPeriod, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]
  all_goals simp [Matrix.fromBlocks_multiply]

variable {A S}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

def complexPhaseChange : ((Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) ⊕
    Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) → ℂ) ≃L[ℂ]
    (((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) ⊕
      (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))) → ℂ) :=
  B.complexPhase.trans ((geometricSplit A S).toContinuousLinearEquiv.trans
    ((B₁.complexPhase.symm.prodCongr B₂.complexPhase.symm).trans IntrinsicPhaseTransport.Intrinsic.joinPhase.toContinuousLinearEquiv))

theorem complexPhaseChange_graph (h₁ : Adelic.DataTheta.GeometryIdentification B₁)
    (h₂ : Adelic.DataTheta.GeometryIdentification B₂) (hB : Adelic.DataTheta.GeometryIdentification B)
    (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    complexPhaseChange B₁ B₂ B
      (Sum.elim ((B.frame z).val.mulVec a) ((B.period z).matrix.mulVec ((B.frame z).val.mulVec a))) =
      Sum.elim ((IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).val.mulVec (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S a))
        ((IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix.mulVec
          ((IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).val.mulVec (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S a))) := by
  change IntrinsicPhaseTransport.Intrinsic.joinPhase
    (B₁.complexPhase.symm ((geometricSplit A S (B.complexPhase _)).1),
     B₂.complexPhase.symm ((geometricSplit A S (B.complexPhase _)).2)) = _
  rw [hB.2.2.2.2.2.2.1, geometricSplit_frame]
  dsimp only [Prod.fst, Prod.snd]
  rw [← h₁.2.2.2.2.2.2.1 z (fun q => a (q.1,q.2.1,0)),
      ← h₂.2.2.2.2.2.2.1 z (fun q => a (q.1,q.2.1,1)),
      ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  have he : IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S a =
      Sum.elim (fun q : Adelic.BallGeometryData.FrameIndex A => a (q.1,q.2.1,0))
        (fun q : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) => a (q.1,q.2.1,1)) := by
    funext i
    cases i <;> rfl
  rw [he]
  exact joinPhase_graph (B₁.period z) (B₂.period z) (B₁.frame z) (B₂.frame z) _ _

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic
