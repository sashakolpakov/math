import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidthArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidthPacking
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidthPrepare

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Width
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram CostAssembly.Polynomial

 def frontEnvelope (C d Z : ℕ) := C*(Z+1)^d
 def packingEnvelope (C d F Z : ℕ) := C*(780*(Z+F)+9*Z+3)^d
 def arithmeticSize (F P Z : ℕ) := Z+F+P+Z+1
 def setupEnvelope (cf df cp dp ca da Z : ℕ) :=
  let F := frontEnvelope cf df Z
  let P := packingEnvelope cp dp F Z
  let A := ca*(arithmeticSize F P Z+1)^da
  (clearCoefficient+51)*(Z+F+P+A+1)+22*Z+42

 theorem setupEnvelope_ordinary (cf df cp dp ca da : ℕ) :
    Ordinary (setupEnvelope cf df cp dp ca da) := by
  have h := ordinary_id
  have hF := ordinary_mul (ordinary_const cf) (ordinary_pow (ordinary_add h (ordinary_const 1)) df)
  have hP := ordinary_mul (ordinary_const cp) (ordinary_pow
    (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 780) (ordinary_add h hF))
      (ordinary_mul (ordinary_const 9) h)) (ordinary_const 3)) dp)
  have hS := ordinary_add (ordinary_add (ordinary_add (ordinary_add h hF) hP) h) (ordinary_const 1)
  have hA := ordinary_mul (ordinary_const ca) (ordinary_pow (ordinary_add hS (ordinary_const 1)) da)
  unfold setupEnvelope frontEnvelope packingEnvelope arithmeticSize
  exact ordinary_add (ordinary_add (ordinary_mul (ordinary_const (clearCoefficient+51))
    (ordinary_add (ordinary_add (ordinary_add (ordinary_add h hF) hP) hA) (ordinary_const 1)))
    (ordinary_mul (ordinary_const 22) h)) (ordinary_const 42)

 theorem model_field_card (x : Input) (l : Fin 8 → ℕ) (hg : Guard x) :
    3^((Execute.guardedModel x l).val 34) ≤ 16*((Execute.guardedModel x l).val 21+1)^2 := by
  have hq : (produce x).Q≠0 := by have := hg.2.2.2.2.2.2.1; omega
  rw [Execute.guardedModel_degree x l hq]
  have he : (Execute.guardedModel x l).val 21=(produce x).Q :=
    (Execute.guardedModel_public x l 4).trans (Layout.model_core_values x l).2.2.2.2.1
  rw [he]
  exact fieldCard_le x

 theorem incoming_width_diagonal : ∃ C d : ℕ, ∀ (q : LeafQueryFrontend.Query) (k : ℕ)
    (a : Data) (hg : Guard (q.input k)) (W V L : ℕ) (p : Preparation q k a hg W V L)
    (Z : ℕ), q.Valid → (∀i,(a.stacks i).length ≤ W) → W ≤ Z → V ≤ Z → L ≤ Z →
    LeafScopeInputBounds.capacity q k ≤ Z →
    (∀i,(Execute.guardedModel (q.input k) p.lengths).val i ≤ Z) →
    (∀i,(Execute.guardedModel (q.input k) p.lengths).len i ≤ Z) →
    incomingWidth p ≤ C*(Z+1)^d := by
  obtain ⟨cf,df,hf⟩ := LeafQueryFrontend.inputBudget_polynomial
  obtain ⟨cp,dp,_,hp⟩ := PackingCallerProgram.budget_polynomial
  obtain ⟨ca,da,ha⟩ := arithmetic_budget_polynomial
  obtain ⟨C,d,hd⟩ := setupEnvelope_ordinary cf df cp dp ca da
  refine ⟨C,d,?_⟩
  intro q k a hg W V L p Z hv hw hW hV hL hc hm hl
  let F := frontEnvelope cf df Z
  let P := packingEnvelope cp dp F Z
  let S := arithmeticSize F P Z
  have hF : q.inputBudget k ≤ F := (hf q k hv).trans (by unfold F frontEnvelope; gcongr)
  have hnf : p.frontSteps ≤ F := p.frontTime.trans hF
  have hfw : ∀i,(p.front.stacks i).length ≤ Z+F := by
    intro i
    exact (eval_width p.frontExecution W hw i).trans (Nat.add_le_add hW hnf)
  have hgsize := packing_globalSize_le q k hg a p.front p.lengths p.bankWords p.frontOutput (Z+F) Z hfw hm
  have hp' := (hp p.front (packingProblem q k hg) p.firstWord p.remainingWords
    (packing_sources q k p.front hg p.lengths p.frontOutput.exported p.frontOutput.scopes
      p.frontOutput.forward p.frontOutput.ambient)
    (packing_empty p.front p.frontOutput.privateEmpty p.frontOutput.spare) p.alphabetOrder).1
  have hP : PackingCallerProgram.budget p.front (packingProblem q k hg) p.firstWord p.remainingWords ≤ P :=
    hp'.trans (by unfold P packingEnvelope; gcongr; omega)
  have hnp : p.packingSteps ≤ P := (Nat.le_of_succ_le p.packingTime).trans hP
  have hZ : Z ≤ S := by unfold S arithmeticSize; omega
  have hR := (packing_scalars q k hg p.lengths Z hm).2.2.2.2.2.2.2.2
  have hR' : (p.packed.stacks 740).length ≤ S := by simpa [p.cutoff] using hR.trans hZ
  have hA := ha (Execute.guardedModel (q.input k) p.lengths)
    (W+q.inputBudget k+PackingCallerProgram.budget p.front (packingProblem q k hg) p.firstWord p.remainingWords)
    V L (p.packed.stacks 740).length S
    (by unfold S arithmeticSize; omega) (hV.trans hZ) (hL.trans hZ) hR'
    (fun i=>(hl i).trans hZ) (fun i=>(hm i).trans hZ) (model_field_card _ _ hg)
  have hna : p.arithmeticSteps ≤ ca*(S+1)^da := p.arithmeticTime.trans hA
  have hn : BinaryArithmetic.toNat q.ambient ≤ Z := (LeafScopeInputBounds.query_bounds q k hv).ambient.trans hc
  apply le_trans _ (hd Z)
  have hb := incomingWidth_le p hw
  unfold setupEnvelope
  change incomingWidth p ≤ (clearCoefficient+51)*(Z+F+P+ca*(S+1)^da+1)+22*Z+42
  exact hb.trans (by gcongr)

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Width

end OAI.Algorithms
