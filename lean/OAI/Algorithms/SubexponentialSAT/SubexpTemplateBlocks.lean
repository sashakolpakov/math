import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateGroups

namespace OAI.Algorithms

/-! The actual outer-block body, including outside descriptors and all
per-color inner traversals. -/

namespace SubexponentialSAT.SubexpTemplateBlocks

open BitProgram StructuredCalls SubexpTemplateProgram SubexpTemplatePacking
open SubexpTemplateTraversal SubexpSelectedConversions SubexpTemplatePointServices
open SubexpTemplateData SubexpTemplateGroups

attribute [local irreducible] SubexpTemplateData.preparedTerm

abbrev Bits := List Bool

def blockWork (input outer : Bits) : Work := {input:=input,outer:=outer}

variable {p D : ℕ} [Fact p.Prime]

def output (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (b : SubexpTemplateData.Block p D) : Bits :=
  SubexpMomentSourceProgram.encodeBlock (preparedBlock ctx source target minusOne b)

def cost (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (b : SubexpTemplateData.Block p D) : ℕ :=
  19*(bankBytes b.base).length+19*(supportBytes b.support).length+
    (2+scanBudget (fun ts => SubexpTemplateProgram.encodeGroup (ts.map rawTerm))
      (groupCost ctx source target minusOne b.base) b.groups)+
    13*(output ctx source target minusOne b).length+64

theorem blockBody_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (b : SubexpTemplateData.Block p D) (regs : Fin 8 → Bool) (rest outer : Bits) :
    ∃ n rf, n ≤ cost ctx source target minusOne b ∧
      Eval blockBody n
        (state ctx regs (blockWork (SubexpTemplateProgram.encodeBlock (rawBlock b) ++ rest) outer))
        (state ctx rf (blockWork rest ((record (output ctx source target minusOne b)).reverse ++ outer))) := by
  let B := bankBytes b.base
  let S := supportBytes b.support
  let G := Encoding.encodeList
    (fun ts => SubexpTemplateProgram.encodeGroup (ts.map rawTerm)) b.groups
  let pref := Encoding.frame B ++ Encoding.frame S
  let records := groupRecords ctx source target minusOne b.base b.groups
  let w0 := blockWork (Encoding.frame B ++ (Encoding.frame S ++ (G ++ rest))) outer
  have hB := capture_field ctx regs w0 .base (by decide) (by decide) B
    (Encoding.frame S ++ (G ++ rest)) rfl rfl rfl
  let r1 := readRegs regs 0 1 none
  let w1 : Work := {base:=B,input:=Encoding.frame S ++ (G ++ rest),outer:=outer}
  have hS := capture_field ctx r1 w1 .support (by decide) (by decide) S (G ++ rest) rfl rfl rfl
  let r2 := readRegs r1 0 1 none
  let w2 : Work := {base:=B,support:=S,input:=G ++ rest,outer:=outer}
  have hfB := appendFrame_field ctx r2 w2 .base .block (by decide) (by decide) (by decide) rfl
  let r3 := afterFrameRegs r2
  let w3 : Work := {w2 with block:=(Encoding.frame B).reverse}
  change Eval (appendFrame 128 131) (8*B.length+7) (state ctx r2 w2)
    (state ctx r3 {w2 with block:=(Encoding.frame B).reverse ++ []}) at hfB
  simp only [List.append_nil] at hfB
  have hfS := appendFrame_field ctx r3 w3 .support .block (by decide) (by decide) (by decide) rfl
  let r4 := afterFrameRegs r3
  let w4 : Work := {w2 with block:=pref.reverse}
  have hpref : (Encoding.frame S).reverse ++ (Encoding.frame B).reverse = pref.reverse := by
    simp only [pref,List.reverse_append]
  change Eval (appendFrame 129 131) (8*S.length+7) (state ctx r3 w3)
    (state ctx r4 {w3 with block:=(Encoding.frame S).reverse ++ (Encoding.frame B).reverse}) at hfS
  rw [hpref] at hfS
  have hclearS := clear_field ctx r4 w4 .support
  let r5 := readRegs r4 0 1 none
  obtain ⟨ng,r6,hng,hg⟩ := groups_eval ctx source target minusOne b.base hc b.groups r5 rest pref.reverse outer
  let w5 := termWork B rest (records.reverse ++ pref.reverse) [] outer
  have hclearB := clear_field ctx r6 w5 .base
  let r7 := readRegs r6 0 1 none
  let w6 : Work := {input:=rest,block:=records.reverse ++ pref.reverse,outer:=outer}
  have hclose := closeList_field ctx r7 w6 .block .outer
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hout : (false :: (records.reverse ++ pref.reverse)).reverse = output ctx source target minusOne b := by
    simp only [List.reverse_cons,List.reverse_append,List.reverse_reverse,
      output,preparedBlock,SubexpMomentSourceProgram.encodeBlock,
      SubexpMomentSourceProgram.encodeDescriptor,
      SubexpBlueprintRows.encodeList_eq_records,
      List.map_map,Function.comp_def]
    rw [List.append_assoc]
    rfl
  change Eval (closeList 131 140) (13*(records.reverse ++ pref.reverse).length+30) (state ctx r7 w6)
    (state ctx (afterFrameRegs r7) (blockWork rest
      ((record (false :: (records.reverse ++ pref.reverse)).reverse).reverse ++ outer))) at hclose
  rw [hout] at hclose
  have h := hB.seq (hS.seq (hfB.seq (hfS.seq (hclearS.seq (hg.seq (hclearB.seq hclose))))))
  refine ⟨_,afterFrameRegs r7,?_,by
    simpa only [blockBody,SubexpTemplateProgram.encodeBlock,rawBlock,
      SubexpBlueprintRows.encodeList_map,blockWork,termWork,
      w0,w1,w2,w3,w4,w5,w6,B,S,G,pref,records,put,fieldValue,Field.port,List.append_assoc] using h⟩
  have hlen := congrArg List.length hout
  simp only [List.length_reverse,List.length_cons,List.length_append] at hlen
  unfold cost
  rw [← hlen]
  simp only [List.length_reverse,List.length_append] at hng ⊢
  dsimp only [B,S,pref,records]
  simp only [List.length_append]
  omega

end SubexponentialSAT.SubexpTemplateBlocks

end OAI.Algorithms
