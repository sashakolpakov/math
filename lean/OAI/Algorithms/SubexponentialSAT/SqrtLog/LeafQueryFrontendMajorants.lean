import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendScanBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramFrontendPoly

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT LeafParametersProgram.FrontendBounds

def parameterSize (S : ℕ) : ℕ := numericMajorant S+2*S^2+2*S+1

def finalMajorant (C d S : ℕ) : ℕ :=
  (10*S+9)+525*scanMajorant S+525*(C*(parameterSize S+1)^d)+6300*S+5514

private theorem variable_poly : Poly (fun S : ℕ => S+1) (fun S => S) :=
  (LeafParametersProgram.FrontendBounds.Poly.self _).mono (fun S => Nat.le_succ S)

theorem numericMajorant_poly : Poly (fun S : ℕ => S+1) numericMajorant := by
  refine ⟨numericMajorant 1,4,?_⟩
  intro S
  have hp (i : ℕ) (hi : i ≤ 4) : S^i ≤ (S+1)^4 :=
    (Nat.pow_le_pow_left (Nat.le_succ S) i).trans (Nat.pow_le_pow_right (by omega) hi)
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  unfold numericMajorant conversionCost
  nlinarith only [h0,h1,h2,h3,h4]

theorem scanMajorant_poly : Poly (fun S : ℕ => S+1) scanMajorant := by
  refine ⟨scanMajorant 1,9,?_⟩
  intro S
  have hp (i : ℕ) (hi : i ≤ 9) : S^i ≤ (S+1)^9 :=
    (Nat.pow_le_pow_left (Nat.le_succ S) i).trans (Nat.pow_le_pow_right (by omega) hi)
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  have h9 := hp 9 (by decide)
  unfold scanMajorant highMajorant measureMajorant numericMajorant conversionCost
    HashScopeProgram.Complete.polynomialBound HashScopeProgram.Complete.rowCostBound
    HashScopeProgram.Complete.optionalCostBound HashScopeProgram.Complete.assemblyBound
    HashScopeProgram.Complete.weightedBytesBound HashInputProgram.Loop.termBudget
    HashInputProgram.LoopDecode.budget SubexpLayoutConstructionBounds.scopeProgramBound
    SubexpLayoutConstructionBounds.scopeCallbackBound SubexpLayoutConstructionBounds.literalBound
    SubexpLayoutConstructionBounds.mappedScopeBytesBound SubexpLiteralChunkProgram.budget
  nlinarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem parameterSize_poly : Poly (fun S : ℕ => S+1) parameterSize := by
  refine ⟨parameterSize 1,4,?_⟩
  intro S
  have hp (i : ℕ) (hi : i ≤ 4) : S^i ≤ (S+1)^4 :=
    (Nat.pow_le_pow_left (Nat.le_succ S) i).trans (Nat.pow_le_pow_right (by omega) hi)
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  unfold parameterSize numericMajorant conversionCost
  nlinarith only [h0,h1,h2,h3,h4]

theorem finalMajorant_poly (C d : ℕ) : Poly (fun S : ℕ => S+1) (finalMajorant C d) := by
  have hp : ∀ S : ℕ, 1 ≤ S+1 := by omega
  have hc := LeafParametersProgram.FrontendBounds.Poly.add hp (LeafParametersProgram.FrontendBounds.Poly.mul (LeafParametersProgram.FrontendBounds.Poly.const _ 10) variable_poly) (LeafParametersProgram.FrontendBounds.Poly.const _ 9)
  have hs := LeafParametersProgram.FrontendBounds.Poly.mul (LeafParametersProgram.FrontendBounds.Poly.const _ 525) scanMajorant_poly
  have hpar := LeafParametersProgram.FrontendBounds.Poly.mul (LeafParametersProgram.FrontendBounds.Poly.const _ 525) (LeafParametersProgram.FrontendBounds.Poly.mul (LeafParametersProgram.FrontendBounds.Poly.const _ C)
    (LeafParametersProgram.FrontendBounds.Poly.pow (LeafParametersProgram.FrontendBounds.Poly.add hp parameterSize_poly (LeafParametersProgram.FrontendBounds.Poly.const _ 1)) d))
  have hn := LeafParametersProgram.FrontendBounds.Poly.mul (LeafParametersProgram.FrontendBounds.Poly.const _ 6300) variable_poly
  exact LeafParametersProgram.FrontendBounds.Poly.add hp (LeafParametersProgram.FrontendBounds.Poly.add hp (LeafParametersProgram.FrontendBounds.Poly.add hp (LeafParametersProgram.FrontendBounds.Poly.add hp hc hs) hpar) hn) (LeafParametersProgram.FrontendBounds.Poly.const _ 5514)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
