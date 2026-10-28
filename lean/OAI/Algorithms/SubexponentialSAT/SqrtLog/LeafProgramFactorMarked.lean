import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorInput

namespace OAI.Algorithms

/-! The marked clause uses the same physical incidence producer, followed by
its direct clause polynomial and one multiplication into the accumulator. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram NativeSemantics

structure MarkedInput {t n d : ℕ} (ctx : Context 3 t n d)
    (minus : RingProgram.Code (Word (baseWidth 3 t)) d)
    (one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (ls : List (SAT.Literal (Fin n))) (a : Data) : Prop where
  raw : a.stacks 154=Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits)
  output : a.stacks 63=[]
  low : ∀ i,a.stacks (Clause.callerStacks (Memory.lowPort i))=IdempotentApplyProgram.Steps.low ctx i
  one : a.stacks 69=Product.bytes one
  minus : a.stacks 76=RingProgram.flat minus
  work : ∀ i ∈ FactorServices.clauseScratch,a.stacks (Clause.callerStacks i)=[]
  seed : a.stacks 151=Product.bytes seed
  temporary : a.stacks 159=[]


theorem markedFactor_eval {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f S B : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (width : List Bool)
    (hw : width.length=baseWidth 3 p.t)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (ls : List (SAT.Literal (Fin n))) (a : Data)
    (sourceWidth : List Bool) (frame : Fin 6 → List Bool)
    (hid : a.stacks 149=(Encoding.encodeNat f).reverse)
    (h556 : a.stacks 556=[]) (h359 : a.stacks 359=[])
    (hready : IncidenceReady p ps P J n f S B theta
      (projectState Incidence.callerRegisters id (FactorID.output a f)) sourceWidth frame)
    (hin : MarkedInput (sourceContext p n u J width hw) minus one seed ls a) :
    let ctx := sourceContext p n u J width hw
    let staged := Incidence.staged (projectState Incidence.callerRegisters id (FactorID.output a f))
    ∃ (payload : ℕ → List Bool) (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
      (k : ℕ) (z : Data),
      (∀ v,payload v.val=Product.bytes (incidence v)) ∧
      (∀ v,Good Finset.univ u J (incidence v)) ∧
      (∀ v,rawDenote p.ops.decode (incidence v)=Squarefree.canonical u J
        (sourceIncidenceJet p ps P n f v.val theta staged.stacks)) ∧
      k ≤ 7*(f+1)+6+
        (incidenceWorkBound p (projectState Incidence.callerRegisters id (FactorID.output a f)) n J S B+1)+
        (9*(a.stacks 154).length+8+
          (FactorServices.clauseBudget ctx minus one incidence
            (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n)=>payload v.val) ()) ls+
            (2*(Squarefree.Program.lookupRecords (HashCircuitProgram.incidenceEntries
              (fun (_ : Unit) (v : Fin n)=>payload v.val) ())).length+3+
              productBudget 3 p.t ctx.modulus ctx.cache ctx.table u J seed
                (FactorServices.clauseResult ctx minus one incidence ls)))) ∧
      Eval markedFactor k a z ∧
      z.stacks=Function.update (Function.update (Function.update (Function.update
        (Function.update a.stacks 154 []) 63 []) 67 []) 62 []) 151
          (Product.bytes (Product.run 3 p.t ctx.modulus ctx.cache ctx.table u J seed
            (FactorServices.clauseResult ctx minus one incidence ls) [])) := by
  dsimp only
  let ctx := sourceContext p n u J width hw
  let staged := Incidence.staged (projectState Incidence.callerRegisters id (FactorID.output a f))
  obtain ⟨payload,ki,mid,hpayload,hki,hi,hm⟩ := prepareIncidence_eval p ps P J n f S B theta a
    sourceWidth frame hid h556 h359 hready
  have hs := hready.caller.staged
  obtain ⟨incidence,hbytes,hgood,hden,hlookup⟩ := payload_family p ps P u J n f hu hJ theta
    staged.stacks payload hs.choicesLength hs.zeroWord hs.oneWord (fun v=>(hpayload v.val v.isLt).2)
  let entries := HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n)=>payload v.val) ()
  have hmove := move_eval mid 154 63 (by decide) (by decide) (by decide)
    (by simpa [hm] using hin.temporary)
  let next := moved mid 154 63
  have hn : next.stacks=Function.update (Function.update mid.stacks 63 (a.stacks 154)) 154 [] := by
    dsimp [next,moved]
    rw [show mid.stacks 154=a.stacks 154 by simp [hm],show mid.stacks 63=[] by simpa [hm] using hin.output]
    simp
  have hnlow : ∀ i,next.stacks (Clause.callerStacks (Memory.lowPort i))=IdempotentApplyProgram.Steps.low ctx i := by
    intro i
    have hne (j : Fin 768) (hj : 56 ≤ j.val) : Clause.callerStacks (Memory.lowPort i)≠j := low_ne i j hj
    rw [hn,hm,Function.update_of_ne (hne 154 (by decide)),Function.update_of_ne (hne 63 (by decide)),
      Function.update_of_ne (hne 62 (by decide))]
    exact hin.low i
  have hnwork : ∀ i ∈ FactorServices.clauseScratch,next.stacks (Clause.callerStacks i)=[] := by
    intro i hi
    have ne : Clause.callerStacks i≠154 ∧ Clause.callerStacks i≠63 ∧ Clause.callerStacks i≠62 :=
      (by decide : ∀ i ∈ FactorServices.clauseScratch,Clause.callerStacks i≠154 ∧
        Clause.callerStacks i≠63 ∧ Clause.callerStacks i≠62) i hi
    rw [hn,hm,Function.update_of_ne ne.1,Function.update_of_ne ne.2.1,Function.update_of_ne ne.2.2]
    exact hin.work i hi
  obtain ⟨kv,z,hkv,hv,hz⟩ := marked_value_eval ctx minus one seed incidence entries hlookup ls next
    hnlow (by simpa [hn] using hin.raw) (by simp [hn,hm,entries])
    (by simpa [hn,hm] using hin.one) (by simpa [hn,hm] using hin.minus) hnwork
    (by simpa [hn,hm] using hin.seed) (by simpa [hn,hm] using hin.temporary)
  have hn62 : next.stacks 62=Squarefree.Program.lookupRecords entries := by simp [hn,hm,entries]
  have hm154 : mid.stacks 154=a.stacks 154 := by simp [hm]
  rw [hn62] at hkv
  refine ⟨payload,incidence,ki+(9*(mid.stacks 154).length+8+kv),z,hbytes,hgood,hden,?_,hi.seq (hmove.seq hv),?_⟩
  · rw [hm154]
    exact Nat.add_le_add hki (Nat.add_le_add_left hkv _)
  · rw [hz,hn,hm]
    funext i
    by_cases h154 : i=154 <;> by_cases h63 : i=63 <;> by_cases h67 : i=67 <;>
      by_cases h62 : i=62 <;> by_cases h151 : i=151 <;>
      simp [Function.update_apply,h154,h63,h67,h62,h151,ctx,sourceContext]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
