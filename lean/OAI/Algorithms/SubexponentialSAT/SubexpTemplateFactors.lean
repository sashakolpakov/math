import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateTraversal
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintExecution

namespace OAI.Algorithms

/-! Actual raw-factor calls and packing inside the one-node template. -/

namespace SubexponentialSAT.SubexpTemplateFactors

open BitProgram StructuredCalls SubexpTemplateProgram SubexpTemplatePacking
open SubexpTemplateTraversal SubexpSelectedConversions SubexpInputBitProgram

abbrev Bits := List Bool
abbrev Factor (p D : ℕ) := List (SubexpBlueprintRows.Row p D)

def pointBytes {p D : ℕ} (point : Fin D → ResidueCode p) : Bits :=
  Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map point)

def contextFor {p D : ℕ} (ctx : Context) (point : Fin D → ResidueCode p) : Context :=
  {ctx with pointStream:=pointBytes point}

def encode {p D : ℕ} (rows : Factor p D) : Bits :=
  Subexp.FactorBlueprint.encodeRows (rows.map SubexpBlueprintRows.Row.packet)

variable {p D : ℕ} [Fact p.Prime]

def output (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (rows : Factor p D) : List SubexpTableSource.Row :=
  SubexpBlueprintExecution.preparedRows (contextFor ctx point) source target minusOne point rows

def cost (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (rows : Factor p D) : ℕ :=
  9*(encode rows).length+
    SubexpBlueprintExecution.runCost (contextFor ctx point) source target minusOne point rows+
    10*(SubexpTableSource.encodeRows (output ctx source target minusOne point rows)).length+19

def emitFactor (bits : Bits) (w : Work) : Work := {w with factors:=bits.reverse ++ w.factors}

/-- The body captures raw rows, invokes the actual beta/Ce/preparation
program, and writes one framed prepared factor. -/
theorem factorBody_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p)
    (hc : SubexpBlueprintCoordinate.ContextGood (contextFor ctx point) source target minusOne point)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (rows : Factor p D) (regs : Fin 8 → Bool) (w : Work) (rest : Bits)
    (hpoint : w.point = pointBytes point) (hfactor : w.factorInput = [])
    (hparser : w.parser = []) (hscratch : w.scratch = []) :
    ∃ n rf, n ≤ cost ctx source target minusOne point rows ∧
      Eval factorBody n
        (state ctx regs {w with input:=Encoding.frame (encode rows) ++ rest})
        (state ctx rf {w with input:=rest,factorInput:=[],factors:=
          (record (SubexpTableSource.encodeRows (output ctx source target minusOne point rows))).reverse ++ w.factors}) := by
  let w0 := {w with input:=Encoding.frame (encode rows) ++ rest}
  have hcapture := capture_field ctx regs w0 .factorInput (by decide) (by decide)
    (encode rows) rest rfl hparser hfactor
  let r1 := readRegs regs 0 1 none
  let w1 := {w with input:=rest,factorInput:=encode rows}
  have hctx : factorContext ctx w1 = contextFor ctx point := by
    unfold factorContext contextFor
    change {ctx with pointStream:=w.point} = {ctx with pointStream:=pointBytes point}
    rw [hpoint]
  obtain ⟨nf,hnf,hf⟩ := SubexpBlueprintExecution.program_runsIn
    (contextFor ctx point) source target minusOne point hc hindex rows r1
  rw [←hctx] at hf
  have hcall := eval_call_from_state SubexpBlueprintFactor.program id factorPorts
    (state ctx r1 w1) Function.injective_id factorPorts_injective
    (by simpa only [project_factor,w1,encode] using hf)
  change Eval _ nf (state ctx r1 w1)
    (embedState id factorPorts (state ctx r1 w1)
      (SubexpBlueprintFactor.serviceState (factorContext ctx w1) (fun _ => false)
        (SubexpTableSource.encodeRows
          (SubexpBlueprintExecution.preparedRows (factorContext ctx w1)
            source target minusOne point rows)))) at hcall
  rw [embed_factor] at hcall
  let bytes := SubexpTableSource.encodeRows (output ctx source target minusOne point rows)
  let w2 := {w1 with factorInput:=bytes}
  have hfctx : SubexpBlueprintExecution.preparedRows (factorContext ctx w1) source target minusOne point rows =
      output ctx source target minusOne point rows := by rw [hctx]; rfl
  rw [hfctx] at hcall
  have hframe := appendRecord_field ctx (fun _ => false) w2 .factorInput .factors
    (by decide) (by decide) (by decide) hscratch
  let r2 := afterFrameRegs (fun _ : Fin 8 => false)
  let w3 := {w2 with factors:=(record bytes).reverse ++ w.factors}
  have hclear := clear_field ctx r2 w3 .factorInput
  have h := hcapture.seq (hcall.seq (hframe.seq hclear))
  refine ⟨_,readRegs r2 0 1 none,?_,by
    simpa only [factorBody,w0,w1,w2,w3,bytes,put,fieldValue,Field.port] using h⟩
  unfold cost
  omega

theorem emitFactor_append (x y : Bits) (w : Work) :
    emitFactor y (emitFactor x w) = emitFactor (x ++ y) w := by
  simp [emitFactor,List.reverse_append,List.append_assoc]

theorem fold_emitFactor {α : Type*} (enc : α → Bits) (xs : List α) (w : Work) :
    xs.foldl (fun w x => emitFactor (enc x) w) w = emitFactor (xs.map enc).flatten w := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.map_cons,List.flatten_cons,emitFactor_append]

def records (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (fs : List (Factor p D)) : Bits :=
  (fs.map (fun rows => record (SubexpTableSource.encodeRows
    (output ctx source target minusOne point rows)))).flatten

/-- Factor iteration is linear in the supplied factor list. Every body call
uses the complete checked raw-factor program; no instruction stream is read. -/
theorem factors_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p)
    (hc : SubexpBlueprintCoordinate.ContextGood (contextFor ctx point) source target minusOne point)
    (hindex : ctx.indexWidth = SubexpSymbolicCost.indexBits ctx.dimension)
    (fs : List (Factor p D)) (regs : Fin 8 → Bool) (w : Work) (rest : Bits)
    (hpoint : w.point = pointBytes point) (hfactor : w.factorInput = [])
    (hparser : w.parser = []) (hscratch : w.scratch = []) :
    ∃ n rf, n ≤ 2+bareBudget (cost ctx source target minusOne point) fs ∧
      Eval (scanBare factorBody) n
        (state ctx regs {w with input:=Encoding.encodeList encode fs ++ rest})
        (state ctx rf {w with input:=rest, factors:=(records ctx source target minusOne point fs).reverse ++ w.factors}) := by
  let enc := fun rows => record (SubexpTableSource.encodeRows (output ctx source target minusOne point rows))
  let Inv := fun w : Work => w.point=pointBytes point ∧ w.factorInput=[] ∧ w.parser=[] ∧ w.scratch=[]
  obtain ⟨n,rf,hn,h⟩ := scanBare_work ctx factorBody encode
    (cost ctx source target minusOne point) (fun rows w => emitFactor (enc rows) w) Inv
    (by
      intro rows rr ww tail hw
      obtain ⟨n,rf,hn,ht⟩ := factorBody_eval ctx source target minusOne point hc hindex rows rr ww tail
        hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
      refine ⟨n,rf,hn,?_⟩
      simpa only [inputState,emitFactor,enc,←hw.2.1] using ht)
    (by intro rows ww hw; exact hw)
    fs regs w rest ⟨hpoint,hfactor,hparser,hscratch⟩
  rw [fold_emitFactor] at h
  exact ⟨n,rf,hn,h⟩

end SubexponentialSAT.SubexpTemplateFactors

end OAI.Algorithms
