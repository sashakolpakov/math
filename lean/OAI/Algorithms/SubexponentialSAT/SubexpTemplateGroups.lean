import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateTerms

namespace OAI.Algorithms

/-! Actual per-color and outer-block loops for the raw template builder. -/

namespace SubexponentialSAT.SubexpTemplateGroups

open BitProgram StructuredCalls SubexpTemplateProgram SubexpTemplatePacking
open SubexpTemplateTraversal SubexpSelectedConversions SubexpTemplatePointServices
open SubexpTemplateData

attribute [local irreducible] SubexpTemplateData.preparedTerm

abbrev Bits := List Bool

def emitGroup (bits : Bits) (w : Work) : Work := {w with group:=bits.reverse ++ w.group}

theorem emitGroup_append (x y : Bits) (w : Work) :
    emitGroup y (emitGroup x w) = emitGroup (x ++ y) w := by
  simp [emitGroup,List.reverse_append,List.append_assoc]

theorem fold_emitGroup {α : Type*} (enc : α → Bits) (xs : List α) (w : Work) :
    xs.foldl (fun w x => emitGroup (enc x) w) w = emitGroup (xs.map enc).flatten w := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.map_cons,List.flatten_cons,emitGroup_append]

variable {p D : ℕ} [Fact p.Prime]

def groupOutput (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (ts : List (SubexpTemplateData.Term p D)) : Bits :=
  SubexpMomentSourceProgram.encodeGroup
    (ts.map (preparedTerm ctx source target minusOne base))

def groupCost (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (ts : List (SubexpTemplateData.Term p D)) : ℕ :=
  scanBudget (fun t => SubexpTemplateProgram.encodeTerm (rawTerm t))
    (termCost ctx source target minusOne base) ts+
    13*(groupOutput ctx source target minusOne base ts).length+20

theorem groupBody_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (ts : List (SubexpTemplateData.Term p D)) (regs : Fin 8 → Bool) (rest block outer : Bits) :
    ∃ n rf, n ≤ groupCost ctx source target minusOne base ts ∧
      Eval groupBody n
        (state ctx regs (termWork (bankBytes base)
          (SubexpTemplateProgram.encodeGroup (ts.map rawTerm) ++ rest) block [] outer))
        (state ctx rf (termWork (bankBytes base) rest
          ((record (groupOutput ctx source target minusOne base ts)).reverse ++ block) [] outer)) := by
  let enc := fun t => record (SubexpMomentSourceProgram.encodeTerm
    (preparedTerm ctx source target minusOne base t))
  let rs := (ts.map enc).flatten
  let Inv := fun w : Work => w = termWork (bankBytes base) w.input w.block w.group w.outer
  obtain ⟨ns,r1,hns,hs⟩ := scan_work ctx termBody
    (fun t => SubexpTemplateProgram.encodeTerm (rawTerm t))
    (termCost ctx source target minusOne base) (fun t w => emitGroup (enc t) w) Inv
    (by intro w hw; rw [hw]; rfl)
    (by
      intro t rr w tail hw
      obtain ⟨n,rf,hn,h⟩ := SubexpTemplateTerms.termBody_eval ctx source target minusOne base hc
        t rr tail w.block w.group w.outer
      refine ⟨n,rf,hn,?_⟩
      apply (congrArg (fun v : Work => Eval termBody n
        (inputState ctx rr v (SubexpTemplateProgram.encodeTerm (rawTerm t) ++ tail))
        (inputState ctx rf (emitGroup (enc t) v) tail)) hw).mpr
      simpa only [inputState,emitGroup,enc,termWork] using h)
    (by intro t w hw; dsimp only [Inv]; rw [hw]; rfl)
    ts regs (termWork (bankBytes base) [] block [] outer) rest rfl
  rw [fold_emitGroup] at hs
  simp only [inputState,emitGroup,termWork,List.append_nil] at hs
  let w1 := termWork (bankBytes base) rest block rs.reverse outer
  have hclose := closeList_field ctx r1 w1 .group .block
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hbytes : (false :: rs.reverse).reverse = groupOutput ctx source target minusOne base ts := by
    simp only [groupOutput,SubexpMomentSourceProgram.encodeGroup,
      SubexpBlueprintRows.encodeList_eq_records,
      List.reverse_cons,List.reverse_reverse,List.map_map,Function.comp_def]
    rfl
  change Eval (closeList 132 131) (13*rs.reverse.length+30) (state ctx r1 w1)
    (state ctx (afterFrameRegs r1) (termWork (bankBytes base) rest
      ((record (false :: rs.reverse).reverse).reverse ++ block) [] outer)) at hclose
  rw [hbytes] at hclose
  have h := hs.seq hclose
  refine ⟨_,afterFrameRegs r1,?_,by
    simpa only [groupBody,SubexpTemplateProgram.encodeGroup,
      SubexpBlueprintRows.encodeList_map,inputState,emitGroup,w1,termWork,rs,enc,
      List.append_nil] using h⟩
  have hlen := congrArg List.length hbytes
  simp only [List.length_reverse,List.length_cons] at hlen
  unfold groupCost
  rw [← hlen]
  simp only [List.length_reverse]
  dsimp only [rs,enc]
  omega

def emitBlock (bits : Bits) (w : Work) : Work := {w with block:=bits.reverse ++ w.block}

theorem emitBlock_append (x y : Bits) (w : Work) :
    emitBlock y (emitBlock x w) = emitBlock (x ++ y) w := by
  simp [emitBlock,List.reverse_append,List.append_assoc]

theorem fold_emitBlock {α : Type*} (enc : α → Bits) (xs : List α) (w : Work) :
    xs.foldl (fun w x => emitBlock (enc x) w) w = emitBlock (xs.map enc).flatten w := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.map_cons,List.flatten_cons,emitBlock_append]

def groupRecords (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (gs : List (List (SubexpTemplateData.Term p D))) : Bits :=
  (gs.map (fun ts => record (groupOutput ctx source target minusOne base ts))).flatten

theorem groups_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (base : Fin D → BaseWord p) (hc : SubexpTemplateData.ContextGood ctx source target minusOne)
    (gs : List (List (SubexpTemplateData.Term p D))) (regs : Fin 8 → Bool) (rest block outer : Bits) :
    ∃ n rf, n ≤ 2+scanBudget
        (fun ts => SubexpTemplateProgram.encodeGroup (ts.map rawTerm))
        (groupCost ctx source target minusOne base) gs ∧
      Eval (scan groupBody) n
        (state ctx regs (termWork (bankBytes base)
          (Encoding.encodeList (fun ts => SubexpTemplateProgram.encodeGroup (ts.map rawTerm)) gs ++ rest)
          block [] outer))
        (state ctx rf (termWork (bankBytes base) rest
          ((groupRecords ctx source target minusOne base gs).reverse ++ block) [] outer)) := by
  let enc := fun ts => record (groupOutput ctx source target minusOne base ts)
  let Inv := fun w : Work => w = termWork (bankBytes base) w.input w.block [] w.outer
  obtain ⟨n,rf,hn,h⟩ := scan_work ctx groupBody
    (fun ts => SubexpTemplateProgram.encodeGroup (ts.map rawTerm))
    (groupCost ctx source target minusOne base) (fun ts w => emitBlock (enc ts) w) Inv
    (by intro w hw; rw [hw]; rfl)
    (by
      intro ts rr w tail hw
      obtain ⟨n,rf,hn,h⟩ := groupBody_eval ctx source target minusOne base hc ts rr tail w.block w.outer
      refine ⟨n,rf,hn,?_⟩
      apply (congrArg (fun v : Work => Eval groupBody n
        (inputState ctx rr v (SubexpTemplateProgram.encodeGroup (ts.map rawTerm) ++ tail))
        (inputState ctx rf (emitBlock (enc ts) v) tail)) hw).mpr
      simpa only [inputState,emitBlock,enc,termWork] using h)
    (by intro ts w hw; dsimp only [Inv]; rw [hw]; rfl)
    gs regs (termWork (bankBytes base) [] block [] outer) rest rfl
  rw [fold_emitBlock] at h
  exact ⟨n,rf,hn,h⟩

end SubexponentialSAT.SubexpTemplateGroups

end OAI.Algorithms
