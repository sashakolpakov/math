import OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport

/-! # Intrinsic Tensor Components -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorComponents.Intrinsic

noncomputable section

/-! Restriction of the actual real tensor components to the two
orthogonal multiplicity lines, including their Hermitian dual components. -/

open scoped _root_.NumberField Classical _root_.Matrix Kronecker _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic

theorem kronecker_block_left {k : Type} [Field k]
    (M : Matrix (Fin 3) (Fin 3) k) (a b : (Matrix (Fin 1) (Fin 1) k)ˣ)
    (x : Fin 3 × Fin 2 → k) (i : Fin 3) :
    ((M ⊗ₖ (IntrinsicSplitting.IntrinsicArithmetic.blockUnit a b).inv).mulVec x) (i,0) =
      ((M ⊗ₖ a.inv).mulVec (fun q : Fin 3 × Fin 1 => x (q.1,0))) (i,0) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, IntrinsicSplitting.IntrinsicArithmetic.blockUnit]

theorem kronecker_block_right {k : Type} [Field k]
    (M : Matrix (Fin 3) (Fin 3) k) (a b : (Matrix (Fin 1) (Fin 1) k)ˣ)
    (x : Fin 3 × Fin 2 → k) (i : Fin 3) :
    ((M ⊗ₖ (IntrinsicSplitting.IntrinsicArithmetic.blockUnit a b).inv).mulVec x) (i,1) =
      ((M ⊗ₖ b.inv).mulVec (fun q : Fin 3 × Fin 1 => x (q.1,1))) (i,0) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, IntrinsicSplitting.IntrinsicArithmetic.blockUnit]

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁) (S : IntrinsicSplitting.IntrinsicSummands.SecondLine A)

theorem geometricSplit_realTensor
    (s : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 2) :
    IntrinsicComplexTransport.Intrinsic.geometricSplit A S (Adelic.BallGeometryData.realTensorComponents (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) s) =
      (Adelic.BallGeometryData.realTensorComponents A (fun v q => s v (q.1,0)),
       Adelic.BallGeometryData.realTensorComponents (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S) (fun v q => s v (q.1,1))) := by
  apply Prod.ext
  · funext v
    apply Prod.ext
    · funext q
      rcases q with ⟨i,r⟩
      fin_cases r
      exact kronecker_block_left (A.basisV v).inv (A.basisP v) (S.basis v)
        (fun q => A.complex v (s v q)) i
    · funext q
      rcases q with ⟨i,r⟩
      fin_cases r
      change (if v = A.distinguished ∧ i = 2 then (-1 : ℂ) else 1) *
        (if A.positive v 0 then 1 else -1) *
          star (((A.basisV v).inv ⊗ₖ (IntrinsicSplitting.IntrinsicArithmetic.blockUnit (A.basisP v) (S.basis v)).inv).mulVec
            (fun q => A.complex v (s v q)) (i,0)) = _
      rw [kronecker_block_left]
      rfl
  · funext v
    apply Prod.ext
    · funext q
      rcases q with ⟨i,r⟩
      fin_cases r
      exact kronecker_block_right (A.basisV v).inv (A.basisP v) (S.basis v)
        (fun q => A.complex v (s v q)) i
    · funext q
      rcases q with ⟨i,r⟩
      fin_cases r
      change (if v = A.distinguished ∧ i = 2 then (-1 : ℂ) else 1) *
        (if S.positive v 0 then 1 else -1) *
          star (((A.basisV v).inv ⊗ₖ (IntrinsicSplitting.IntrinsicArithmetic.blockUnit (A.basisP v) (S.basis v)).inv).mulVec
            (fun q => A.complex v (s v q)) (i,1)) = _
      rw [kronecker_block_right]
      rfl

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorComponents.Intrinsic
