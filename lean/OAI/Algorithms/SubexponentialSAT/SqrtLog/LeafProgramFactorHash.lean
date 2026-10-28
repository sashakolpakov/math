import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorInput

namespace OAI.Algorithms

/-! The complete ordinary-factor branch uses the actual returned incidence
bytes, including their source-polynomial meaning. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram NativeSemantics


theorem hashFactor_eval {r Q n d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J f S B : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d) (width : List Bool)
    (hw : width.length=baseWidth 3 p.t)
    (minus : RingProgram.Code (Word (baseWidth 3 p.t)) d)
    (one seed : Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 p.t)))
    (b : ℕ) (hb : 0 < b) (hbound : 3*(HashInputProgram.Expansion.encodedClauses source).length ≤ 2^b)
    (a : Data) (sourceWidth : List Bool) (frame : Fin 6 → List Bool)
    (hid : a.stacks 149=(Encoding.encodeNat f).reverse) (h556 : a.stacks 556=[])
    (hready : IncidenceReady p ps P J n f S B theta
      (projectState Incidence.callerRegisters id (FactorID.output a f)) sourceWidth frame)
    (hin : HashInput (sourceContext p n u J width hw) minus one seed source terms digits b a) :
    let ctx := sourceContext p n u J width hw
    let staged := Incidence.staged (projectState Incidence.callerRegisters id (FactorID.output a f))
    let ws := HashInputProgram.Expansion.weightedRow p.t d source terms
    ∃ (payload : ℕ → List Bool) (incidence : Fin n → Raw (p:=3) (t:=p.t) (n:=n) (d:=d))
      (k : ℕ) (z : Data),
      (∀ v,payload v.val=Product.bytes (incidence v)) ∧
      (∀ v,Good Finset.univ u J (incidence v)) ∧
      (∀ v,rawDenote p.ops.decode (incidence v)=Squarefree.canonical u J
        (sourceIncidenceJet p ps P n f v.val theta staged.stacks)) ∧
      k ≤ 7*(f+1)+6+
        (incidenceWorkBound p (projectState Incidence.callerRegisters id (FactorID.output a f)) n J S B+1)+
        (9*(a.stacks 154).length+10+
          HashInputProgram.Loop.uniformBudget p.t (d-1) b (a.stacks 707)
            (HashInputProgram.Expansion.encodedClauses source) terms.length+
          FactorServices.indicatorBudget ctx minus one incidence
            (HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n)=>payload v.val) ()) ws digits+
          (2*(Product.bytes (Indicator.rawHash ctx minus one incidence ws)).length+
            2*(Squarefree.Program.lookupRecords (HashCircuitProgram.incidenceEntries
              (fun (_ : Unit) (v : Fin n)=>payload v.val) ())).length+6+
            productBudget 3 p.t ctx.modulus ctx.cache ctx.table u J seed
              (Indicator.result ctx minus one incidence ws digits))) ∧
      Eval hashFactor k a z ∧
      z.stacks=Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update a.stacks 154 []) 64 []) 67 []) 68 []) 62 []) 151
          (Product.bytes (Product.run 3 p.t ctx.modulus ctx.cache ctx.table u J seed
            (Indicator.result ctx minus one incidence ws digits) [])) := by
  dsimp only
  let ctx := sourceContext p n u J width hw
  let staged := Incidence.staged (projectState Incidence.callerRegisters id (FactorID.output a f))
  let ws := HashInputProgram.Expansion.weightedRow p.t d source terms
  obtain ⟨payload,ki,mid,hpayload,hki,hi,hm⟩ := prepareIncidence_eval p ps P J n f S B theta a
    sourceWidth frame hid h556 hin.work359 hready
  have hs := hready.caller.staged
  obtain ⟨incidence,hbytes,hgood,hden,hlookup⟩ := payload_family p ps P u J n f hu hJ theta
    staged.stacks payload hs.choicesLength hs.zeroWord hs.oneWord (fun v=>(hpayload v.val v.isLt).2)
  have hmid : HashInput ctx minus one seed source terms digits b mid := hin.frame (by
    intro i hi
    rw [hm,Function.update_of_ne hi])
  let entries := HashCircuitProgram.incidenceEntries (fun (_ : Unit) (v : Fin n)=>payload v.val) ()
  obtain ⟨kh,z,hkh,hh,hz⟩ := expanded_hash_eval ctx p.ht p.hd minus one seed incidence entries hlookup
    source terms digits b hb hbound mid hmid.raw hmid.formula hmid.width hmid.modulus hmid.ringShape
    hmid.output hmid.expand hmid.work358 hmid.work359 hmid.low (by rw [hm]; simp [entries])
    hmid.one hmid.minus hmid.tape hmid.shape hmid.work hmid.seed hmid.temporary
  have hm154 : mid.stacks 154=a.stacks 154 := by simp [hm]
  have hm707 : mid.stacks 707=a.stacks 707 := by simp [hm]
  have hm62 : mid.stacks 62=Squarefree.Program.lookupRecords entries := by simp [hm,entries]
  rw [hm154,hm707,hm62] at hkh
  refine ⟨payload,incidence,ki+kh,z,hbytes,hgood,hden,?_,hi.seq hh,?_⟩
  · change kh ≤ _ at hkh
    dsimp only [ctx,sourceContext] at hkh ⊢
    exact Nat.add_le_add hki hkh
  · rw [hz,hm]
    funext i
    by_cases h154 : i=154 <;> by_cases h64 : i=64 <;> by_cases h67 : i=67 <;>
      by_cases h68 : i=68 <;> by_cases h62 : i=62 <;> by_cases h151 : i=151 <;>
      simp [Function.update_apply,h154,h64,h67,h68,h62,h151,ctx,sourceContext]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
