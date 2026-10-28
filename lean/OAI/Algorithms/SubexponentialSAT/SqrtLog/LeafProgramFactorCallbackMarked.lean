import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorJet
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorCallbackFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemanticsFactors

namespace OAI.Algorithms

/-! Complete marked-clause ID callback with paid role dispatch and cleanup. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram NativeSemantics

theorem callback_marked_native {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f S B : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (width : List Bool)
    (hw : width.length=baseWidth 3 p.t)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (hone : Good Finset.univ u J one) (hseed : Good Finset.univ u J seed)
    (ls : List (SAT.Literal (Fin n)))
    (a : Data) (rows clauses : List (List Bool)) (marked : Bool) (mark : ℕ)
    (hrows : a.stacks 701=Encoding.encodeList id rows)
    (hclauses : a.stacks 700=Encoding.encodeList id clauses)
    (hcount : a.stacks 704=List.replicate rows.length true)
    (hmark : a.stacks 705=Encoding.encodeNat mark) (hflag : a.stacks 706=[marked])
    (hfactor : a.stacks 149=(Encoding.encodeNat f).reverse)
    (hwork : ∀ i ∈ FactorDispatch.scratch,a.stacks i=[])
    (hvalid : marked=true → mark < clauses.length) (hhash : ¬ f < rows.length)
    (hmarked : (marked && decide (f=rows.length))=true)
    (hblank : ∀ i ∈ ([154,63,67,62] : List (Fin 768)),a.stacks i=[])
    (h556 : a.stacks 556=[]) (sourceWidth : List Bool) (frame : Fin 6 → List Bool)
    (hready : ∀ rd : Fin 8 → Bool, IncidenceReady p ps P J n f S B theta
      (projectState Incidence.callerRegisters id
        (FactorID.output (FactorDispatch.finished a rd rows clauses marked mark f) f)) sourceWidth frame)
    (hin : ∀ rd : Fin 8 → Bool, MarkedInput (sourceContext p n u J width hw) minus one seed ls
      (FactorDispatch.finished a rd rows clauses marked mark f)) :
    let ctx := sourceContext p n u J width hw
    ∃ (rd : Fin 8 → Bool) (payload : ℕ → List Bool)
      (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d)) (k : ℕ) (z : Data),
      (∀ v,payload v.val=Product.bytes (incidence v)) ∧
      (∀ v,Good Finset.univ u J (incidence v)) ∧
      (∀ v,rawDenote p.ops.decode (incidence v)=Squarefree.canonical u J
        (factorJet p ps P n f v.val theta a.stacks)) ∧
      Good Finset.univ u J (MomentsProgram.Product.run 3 p.t ctx.modulus ctx.cache ctx.table u J seed
        (FactorServices.clauseResult ctx minus one incidence ls) []) ∧
      k ≤ 7*(a.stacks 149).length+6+LeafFactorDispatchProgram.budget rows clauses mark f+
        (2+markedBranchBudget p ctx f S B minus one seed ls
          (FactorDispatch.finished a rd rows clauses marked mark f) payload incidence+
          (2*(a.stacks 149).length+6)) ∧
      Eval callback k a z ∧
      z.stacks=Function.update (Function.update a.stacks 149 []) 151
        (Product.bytes (MomentsProgram.Product.run 3 p.t ctx.modulus ctx.cache ctx.table u J seed
          (FactorServices.clauseResult ctx minus one incidence ls) [])) ∧
      z.regs 13=false ∧ z.regs 14=true ∧ z.regs 15=false := by
  dsimp only
  let ctx := sourceContext p n u J width hw
  obtain ⟨kd,rd,hkd,hd,h5,h6,h7⟩ := FactorDispatch.command_eval a rows clauses marked mark f
    hrows hclauses hcount hmark hflag hfactor hwork hvalid
  let mid := FactorDispatch.finished a rd rows clauses marked mark f
  have hm : mid.stacks=Function.update a.stacks 154
      (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark f) :=
    FactorDispatch.finished_stacks a rd rows clauses marked mark f hrows hclauses hcount hmark hwork
  have hm5 : mid.regs 5=false := by
    rw [FactorDispatch.finished_role_hash,h5]
    exact decide_eq_false hhash
  have hm6 : mid.regs 6=true := by rw [FactorDispatch.finished_role_marked,h6,hmarked]
  obtain ⟨payload,incidence,kf,endFactor,hbytes,hgood,hden,hkf,hf,hend⟩ := markedFactor_eval p ps P
    u J f S B hu hJ theta width hw minus one seed ls mid sourceWidth frame
    (by simpa [hm] using hfactor) (by simpa [hm] using h556)
    (by simpa [hm] using hwork 359 (by simp [FactorDispatch.scratch])) (hready rd) (hin rd)
  have hden' (v : Fin n) : rawDenote p.ops.decode (incidence v)=Squarefree.canonical u J
      (factorJet p ps P n f v.val theta a.stacks) := by
    rw [hden v]
    congr 1
    exact (factorJet_staged p ps P J n f v.val theta _ (hready rd).caller).trans
      (factorJet_frame p ps P n f v.val theta _ a.stacks
        (by change (FactorID.output mid f).stacks 145=a.stacks 145; simp [FactorID.output,hm])
        (by change (FactorID.output mid f).stacks 702=a.stacks 702; simp [FactorID.output,hm])
        (by change (FactorID.output mid f).stacks 703=a.stacks 703; simp [FactorID.output,hm]))
  have hchoose : Eval choose ((kf+1)+1) mid endFactor := Eval.ite_false hm5 (Eval.ite_true hm6 hf)
  have hgoodFactor : Good Finset.univ u J (FactorServices.clauseResult ctx minus one incidence ls) :=
    clause_fold_good 3 p.t ctx.modulus ctx.cache ctx.table Finset.univ u J minus one incidence
      hone hgood ls one hone
  have hgoodOut := product_good 3 p.t ctx.modulus ctx.cache ctx.table Finset.univ u J seed
    (FactorServices.clauseResult ctx minus one incidence ls) hseed hgoodFactor
  have heq : endFactor.stacks=Function.update a.stacks 151
      (Product.bytes (MomentsProgram.Product.run 3 p.t ctx.modulus ctx.cache ctx.table u J seed
        (FactorServices.clauseResult ctx minus one incidence ls) [])) := by
    rw [hend,hm]
    exact marked_updates a.stacks _ _ (hblank 154 (by simp)) (hblank 63 (by simp)) (hblank 67 (by simp)) (hblank 62 (by simp))
  have h149 : endFactor.stacks 149=a.stacks 149 := by simp [heq]
  have hfinish := callbackFinish_eval endFactor
  refine ⟨rd,payload,incidence,kd+((kf+1)+1+(2*(endFactor.stacks 149).length+6)),
    callbackFinished endFactor,hbytes,hgood,hden',hgoodOut,?_,hd.seq (hchoose.seq hfinish),?_,
    callbackFinished_tag _,callbackFinished_present _,callbackFinished_found _⟩
  · rw [h149]
    change kf ≤ markedBranchBudget p ctx f S B minus one seed ls mid payload incidence at hkf
    dsimp only [ctx,mid] at hkf
    omega
  · rw [callbackFinished_stacks,heq]
    exact callback_updates a.stacks _

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
