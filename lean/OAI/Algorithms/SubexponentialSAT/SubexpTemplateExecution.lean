import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateBlocks

namespace OAI.Algorithms

/-! Complete measured execution of the fixed raw-template controller. -/

namespace SubexponentialSAT.SubexpTemplateExecution

open BitProgram StructuredCalls SubexpTemplateProgram SubexpTemplatePacking
open SubexpTemplateTraversal SubexpSelectedConversions SubexpTemplateData
open SubexpTemplateBlocks

attribute [local irreducible] SubexpTemplateData.preparedTerm SubexpTemplateData.preparedBlock

abbrev Bits := List Bool

def emitOuter (bits : Bits) (w : Work) : Work := {w with outer:=bits.reverse ++ w.outer}

theorem emitOuter_append (x y : Bits) (w : Work) :
    emitOuter y (emitOuter x w) = emitOuter (x ++ y) w := by
  simp [emitOuter,List.reverse_append,List.append_assoc]

theorem fold_emitOuter {α : Type*} (enc : α → Bits) (xs : List α) (w : Work) :
    xs.foldl (fun w x => emitOuter (enc x) w) w = emitOuter (xs.map enc).flatten w := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.map_cons,List.flatten_cons,emitOuter_append]

variable {p D : ℕ} [Fact p.Prime]

def output (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (bs : List (SubexpTemplateData.Block p D)) : Bits :=
  SubexpMomentSourceProgram.encodeTemplate (bs.map (preparedBlock ctx source target minusOne))

def runCost (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (bs : List (SubexpTemplateData.Block p D)) : ℕ :=
  scanBudget (fun b => SubexpTemplateProgram.encodeBlock (rawBlock b))
    (SubexpTemplateBlocks.cost ctx source target minusOne) bs+
    3*(output ctx source target minusOne bs).length+8

theorem command_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (bs : List (SubexpTemplateData.Block p D)) (regs : Fin 8 → Bool) :
    ∃ n rf, n+1 ≤ runCost ctx source target minusOne bs ∧
      Eval command n
        (serviceState ctx regs (SubexpTemplateProgram.encodeBlocks (bs.map rawBlock)))
        (state ctx rf {output:=output ctx source target minusOne bs}) := by
  let enc := fun b => record (SubexpTemplateBlocks.output ctx source target minusOne b)
  let records := (bs.map enc).flatten
  let Inv := fun w : Work => w = blockWork w.input w.outer
  obtain ⟨ns,rs,hns,hs⟩ := scan_work ctx blockBody
    (fun b => SubexpTemplateProgram.encodeBlock (rawBlock b))
    (SubexpTemplateBlocks.cost ctx source target minusOne) (fun b w => emitOuter (enc b) w) Inv
    (by intro w hw; rw [hw]; rfl)
    (by
      intro b rr w tail hw
      obtain ⟨n,rf,hn,h⟩ := blockBody_eval ctx source target minusOne hc b rr tail w.outer
      refine ⟨n,rf,hn,?_⟩
      apply (congrArg (fun v : Work => Eval blockBody n
        (inputState ctx rr v (SubexpTemplateProgram.encodeBlock (rawBlock b) ++ tail))
        (inputState ctx rf (emitOuter (enc b) v) tail)) hw).mpr
      simpa only [inputState,emitOuter,enc,blockWork] using h)
    (by intro b w hw; dsimp only [Inv]; rw [hw]; rfl)
    bs regs (blockWork [] []) [] rfl
  rw [fold_emitOuter] at hs
  simp only [inputState,emitOuter,blockWork,List.append_nil] at hs
  let w1 := blockWork [] records.reverse
  have hp := push_field ctx rs w1 .outer false
  let rp := Function.update rs 0 false
  let w2 := blockWork [] (false :: records.reverse)
  have ht := transfer_field ctx rp w2 .outer .output (by decide)
  have hbytes : (false :: records.reverse).reverse = output ctx source target minusOne bs := by
    simp only [output,SubexpMomentSourceProgram.encodeTemplate,
      SubexpBlueprintRows.encodeList_eq_records,
      List.reverse_cons,List.reverse_reverse,List.map_map,Function.comp_def]
    rfl
  change Eval (transfer 140 139) (3*(false :: records.reverse).length+3) (state ctx rp w2)
    (state ctx (readRegs rp 0 1 none) {output:=(false :: records.reverse).reverse ++ []}) at ht
  rw [hbytes,List.append_nil] at ht
  have h := hs.seq (hp.seq ht)
  refine ⟨_,readRegs rp 0 1 none,?_,by
    simpa only [command,serviceState,SubexpTemplateProgram.encodeBlocks,
      SubexpBlueprintRows.encodeList_map,inputState,emitOuter,blockWork,
      w1,w2,records,enc,put,fieldValue,Field.port,List.append_nil] using h⟩
  have hlen := congrArg List.length hbytes
  simp only [List.length_reverse,List.length_cons] at hlen
  unfold runCost
  rw [← hlen]
  simp only [List.length_reverse,List.length_cons] at hns ⊢
  dsimp only [records,enc]
  omega

theorem program_runsIn (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (bs : List (SubexpTemplateData.Block p D)) (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn program (runCost ctx source target minusOne bs)
      ((serviceState ctx regs (SubexpTemplateProgram.encodeBlocks (bs.map rawBlock))).withPC
        (some program.entry))
      ((state ctx rf {output:=output ctx source target minusOne bs}).withPC none) := by
  obtain ⟨n,rf,hn,h⟩ := command_eval ctx source target minusOne hc bs regs
  exact ⟨rf,n+1,hn,compiled_halt_trace h 130 139⟩

theorem primitive_execution (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (bs : List (SubexpTemplateData.Block p D)) (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (primitiveOverhead program * runCost ctx source target minusOne bs)
      (primitiveCfg program ((serviceState ctx regs
        (SubexpTemplateProgram.encodeBlocks (bs.map rawBlock))).withPC (some program.entry)))
      (primitiveCfg program ((state ctx rf {output:=output ctx source target minusOne bs}).withPC none)) := by
  obtain ⟨rf,h⟩ := program_runsIn ctx source target minusOne hc bs regs
  exact ⟨rf,BitProgram.primitive_execution program h⟩

end SubexponentialSAT.SubexpTemplateExecution

end OAI.Algorithms
