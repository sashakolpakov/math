import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorJet
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorCallbackFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemanticsFactors

namespace OAI.Algorithms

/-! Complete ordinary-ID callbacks, including actual dispatch, source/row
execution, accumulation, and parser restoration. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram NativeSemantics

theorem callback_hash_native {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f S B : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (width : List Bool)
    (hw : width.length=baseWidth 3 p.t)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hone : Good Finset.univ u J one) (hseed : Good Finset.univ u J seed)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 p.t)))
    (b : ℕ) (hb : 0 < b) (hbound : 3*(HashInputProgram.Expansion.encodedClauses source).length ≤ 2^b)
    (a : Data) (rows clauses : List (List Bool)) (marked : Bool) (mark : ℕ)
    (hrows : a.stacks 701=Encoding.encodeList id rows)
    (hclauses : a.stacks 700=Encoding.encodeList id clauses)
    (hcount : a.stacks 704=List.replicate rows.length true)
    (hmark : a.stacks 705=Encoding.encodeNat mark) (hflag : a.stacks 706=[marked])
    (hfactor : a.stacks 149=(Encoding.encodeNat f).reverse)
    (hwork : ∀ i ∈ FactorDispatch.scratch,a.stacks i=[])
    (hvalid : marked=true → mark < clauses.length) (hhash : f < rows.length)
    (hblank : ∀ i ∈ ([154,64,67,68,62] : List (Fin 768)),a.stacks i=[])
    (h556 : a.stacks 556=[]) (sourceWidth : List Bool) (frame : Fin 6 → List Bool)
    (hready : ∀ rd : Fin 8 → Bool, IncidenceReady p ps P J n f S B theta
      (projectState Incidence.callerRegisters id
        (FactorID.output (FactorDispatch.finished a rd rows clauses marked mark f) f)) sourceWidth frame)
    (hin : ∀ rd : Fin 8 → Bool, HashInput (sourceContext p n u J width hw) minus one seed source terms digits b
      (FactorDispatch.finished a rd rows clauses marked mark f)) :
    let ctx := sourceContext p n u J width hw
    let ws := HashInputProgram.Expansion.weightedRow p.t d source terms
    ∃ (rd : Fin 8 → Bool) (payload : ℕ → List Bool)
      (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)) (k : ℕ) (z : Data),
      (∀ v,payload v.val=Product.bytes (incidence v)) ∧
      (∀ v,Good Finset.univ u J (incidence v)) ∧
      (∀ v,rawDenote p.ops.decode (incidence v)=Squarefree.canonical u J
        (factorJet p ps P n f v.val theta a.stacks)) ∧
      Good Finset.univ u J (MomentsProgram.Product.run 3 p.t ctx.modulus ctx.cache ctx.table u J seed
        (Indicator.result ctx minus one incidence ws digits) []) ∧
      k ≤ 7*(a.stacks 149).length+6+LeafFactorDispatchProgram.budget rows clauses mark f+
        (1+hashBranchBudget p ctx f S B minus one seed source terms digits b
          (FactorDispatch.finished a rd rows clauses marked mark f) payload incidence+
          (2*(a.stacks 149).length+6)) ∧
      Eval callback k a z ∧
      z.stacks=Function.update (Function.update a.stacks 149 []) 151
        (Product.bytes (MomentsProgram.Product.run 3 p.t ctx.modulus ctx.cache ctx.table u J seed
          (Indicator.result ctx minus one incidence ws digits) [])) ∧
      z.regs 13=false ∧ z.regs 14=true ∧ z.regs 15=false := by
  dsimp only
  let ctx := sourceContext p n u J width hw
  obtain ⟨kd,rd,hkd,hd,h5,h6,h7⟩ := FactorDispatch.command_eval a rows clauses marked mark f
    hrows hclauses hcount hmark hflag hfactor hwork hvalid
  let mid := FactorDispatch.finished a rd rows clauses marked mark f
  have hm : mid.stacks=Function.update a.stacks 154
      (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark f) :=
    FactorDispatch.finished_stacks a rd rows clauses marked mark f hrows hclauses hcount hmark hwork
  have hm5 : mid.regs 5=true := by
    rw [FactorDispatch.finished_role_hash,h5]
    exact decide_eq_true hhash
  obtain ⟨payload,incidence,kf,endFactor,hbytes,hgood,hden,hkf,hf,hend⟩ := hashFactor_eval p ps P
    u J f S B hu hJ theta width hw minus one seed source terms digits b hb hbound mid sourceWidth frame
    (by simpa [hm] using hfactor) (by simpa [hm] using h556) (hready rd) (hin rd)
  have hden' (v : Fin n) : rawDenote p.ops.decode (incidence v)=Squarefree.canonical u J
      (factorJet p ps P n f v.val theta a.stacks) := by
    rw [hden v]
    congr 1
    exact (factorJet_staged p ps P J n f v.val theta _ (hready rd).caller).trans
      (factorJet_frame p ps P n f v.val theta _ a.stacks
        (by change (FactorID.output mid f).stacks 145=a.stacks 145; simp [FactorID.output,hm])
        (by change (FactorID.output mid f).stacks 702=a.stacks 702; simp [FactorID.output,hm])
        (by change (FactorID.output mid f).stacks 703=a.stacks 703; simp [FactorID.output,hm]))
  have hchoose : Eval choose (kf+1) mid endFactor := Eval.ite_true hm5 hf
  have hgoodFactor := AssignmentSemantics.indicator_good ctx Finset.univ hu hJ minus one incidence
    hone hgood (HashInputProgram.Expansion.weightedRow p.t d source terms) digits
  have hgoodOut := product_good 3 p.t ctx.modulus ctx.cache ctx.table Finset.univ u J seed
    (Indicator.result ctx minus one incidence (HashInputProgram.Expansion.weightedRow p.t d source terms) digits)
    hseed hgoodFactor
  have heq : endFactor.stacks=Function.update a.stacks 151
      (Product.bytes (MomentsProgram.Product.run 3 p.t ctx.modulus ctx.cache ctx.table u J seed
        (Indicator.result ctx minus one incidence (HashInputProgram.Expansion.weightedRow p.t d source terms) digits) [])) := by
    rw [hend,hm]
    exact hash_updates a.stacks _ _ (hblank 154 (by simp)) (hblank 64 (by simp)) (hblank 67 (by simp)) (hblank 68 (by simp)) (hblank 62 (by simp))
  have h149 : endFactor.stacks 149=a.stacks 149 := by simp [heq]
  have hfinish := callbackFinish_eval endFactor
  refine ⟨rd,payload,incidence,kd+(kf+1+(2*(endFactor.stacks 149).length+6)),
    callbackFinished endFactor,hbytes,hgood,hden',hgoodOut,?_,hd.seq (hchoose.seq hfinish),?_,
    callbackFinished_tag _,callbackFinished_present _,callbackFinished_found _⟩
  · rw [h149]
    change kf ≤ hashBranchBudget p ctx f S B minus one seed source terms digits b mid payload incidence at hkf
    dsimp only [ctx,mid] at hkf
    omega
  · rw [callbackFinished_stacks,heq]
    exact callback_updates a.stacks _

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
