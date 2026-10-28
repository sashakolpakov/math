import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintCoordinate

namespace OAI.Algorithms

/-! Serial coordinate and row traversal for the raw factor producer. -/

namespace SubexponentialSAT.SubexpBlueprintRows

open BitProgram StructuredCalls SubexpBlueprintFactor SubexpBlueprintPacking
open SubexpBlueprintTraversal SubexpBlueprintCoordinate
open SubexpSelectedConversions SubexpInputBitProgram

abbrev Bits := List Bool

structure Row (p D : ℕ) where
  value : Bits
  coordinates : List (SubexpBlueprintCoordinate.Coordinate p D)

def Row.packet {p D : ℕ} (r : Row p D) : Subexp.FactorBlueprint.Row :=
  ⟨r.value,r.coordinates.map SubexpBlueprintCoordinate.Coordinate.packet⟩

def encode {p D : ℕ} (r : Row p D) : Bits :=
  Subexp.FactorBlueprint.encodeRow r.packet

def emitRow (bits : Bits) (w : Work) : Work := {w with row:=bits.reverse ++ w.row}
def emitFactor (bits : Bits) (w : Work) : Work := {w with factor:=bits.reverse ++ w.factor}

def Clean (w : Work) : Prop := w = baseWork w.input w.row w.factor

theorem clean_base (input row factor : Bits) : Clean (baseWork input row factor) := rfl

theorem clean_emitRow (bits : Bits) (w : Work) (hw : Clean w) : Clean (emitRow bits w) := by
  unfold Clean at hw ⊢
  rw [hw]
  rfl

theorem clean_emitFactor (bits : Bits) (w : Work) (hw : Clean w) : Clean (emitFactor bits w) := by
  unfold Clean at hw ⊢
  rw [hw]
  rfl

theorem emitRow_append (x y : Bits) (w : Work) :
    emitRow y (emitRow x w) = emitRow (x ++ y) w := by
  simp [emitRow,List.reverse_append,List.append_assoc]

theorem emitFactor_append (x y : Bits) (w : Work) :
    emitFactor y (emitFactor x w) = emitFactor (x ++ y) w := by
  simp [emitFactor,List.reverse_append,List.append_assoc]

theorem fold_emitRow {α : Type*} (enc : α → Bits) (xs : List α) (w : Work) :
    xs.foldl (fun w x => emitRow (enc x) w) w = emitRow (xs.map enc).flatten w := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.map_cons,List.flatten_cons,emitRow_append]

theorem fold_emitFactor {α : Type*} (enc : α → Bits) (xs : List α) (w : Work) :
    xs.foldl (fun w x => emitFactor (enc x) w) w = emitFactor (xs.map enc).flatten w := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.map_cons,List.flatten_cons,emitFactor_append]

theorem encodeList_map {α β : Type*} (enc : β → Bits) (f : α → β) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,Encoding.encodeList,ih]

theorem encode_eq {p D : ℕ} (r : Row p D) :
    encode r = Encoding.frame r.value ++
      Encoding.encodeList SubexpBlueprintCoordinate.encode r.coordinates := by
  unfold encode Row.packet Subexp.FactorBlueprint.encodeRow
  rw [encodeList_map]
  rfl

theorem encodeRows_eq {p D : ℕ} (rows : List (Row p D)) :
    Subexp.FactorBlueprint.encodeRows (rows.map Row.packet) =
      Encoding.encodeList encode rows := by
  unfold Subexp.FactorBlueprint.encodeRows
  rw [encodeList_map]
  rfl

theorem encodeList_eq_records {α : Type*} (enc : α → Bits) (xs : List α) :
    Encoding.encodeList enc xs = (xs.map (fun x => record (enc x))).flatten ++ [false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList,ih,record,List.append_assoc]

variable {p D : ℕ} [Fact p.Prime]

def output (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (r : Row p D) : SubexpTableSource.Row :=
  ⟨r.value,r.coordinates.map (SubexpBlueprintCoordinate.output ctx source target minusOne point)⟩

def coordinateRecords (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (cs : List (SubexpBlueprintCoordinate.Coordinate p D)) : Bits :=
  (cs.map (fun c => record (SubexpTableSource.encodeCoordinate
    (SubexpBlueprintCoordinate.output ctx source target minusOne point c)))).flatten

def cost (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (r : Row p D) : ℕ :=
  19*r.value.length+19+
    (2+scanBudget SubexpBlueprintCoordinate.encode
      (SubexpBlueprintCoordinate.cost ctx source target minusOne point) r.coordinates)+
    13*((Encoding.frame r.value ++ coordinateRecords ctx source target minusOne point r.coordinates).length)+30

theorem coordinates_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p)
    (hc : SubexpBlueprintCoordinate.ContextGood ctx source target minusOne point)
    (cs : List (SubexpBlueprintCoordinate.Coordinate p D))
    (regs : Fin 8 → Bool) (rest row factor : Bits) :
    ∃ n rf, n ≤ 2+scanBudget SubexpBlueprintCoordinate.encode
        (SubexpBlueprintCoordinate.cost ctx source target minusOne point) cs ∧
      Eval (scan coordinateBody) n
        (state ctx regs (baseWork
          (Encoding.encodeList SubexpBlueprintCoordinate.encode cs ++ rest) row factor))
        (state ctx rf (baseWork rest
          ((coordinateRecords ctx source target minusOne point cs).reverse ++ row) factor)) := by
  let enc := fun c => record (SubexpTableSource.encodeCoordinate
    (SubexpBlueprintCoordinate.output ctx source target minusOne point c))
  obtain ⟨n,rf,hn,h⟩ := scan_work ctx coordinateBody SubexpBlueprintCoordinate.encode
    (SubexpBlueprintCoordinate.cost ctx source target minusOne point)
    (fun c w => emitRow (enc c) w) Clean
    (by intro w hw; rw [show w = baseWork w.input w.row w.factor from hw]; rfl)
    (by
      intro c r w tail hw
      obtain ⟨n,rf,hn,h⟩ := coordinateBody_eval ctx source target minusOne point hc c r tail w.row w.factor
      refine ⟨n,rf,hn,?_⟩
      have hw' : w = baseWork w.input w.row w.factor := hw
      have hs := congrArg (fun z => inputState ctx r z
        (SubexpBlueprintCoordinate.encode c ++ tail)) hw'
      have he := congrArg (fun z => inputState ctx rf (emitRow (enc c) z) tail) hw'
      rw [hs,he]
      exact h)
    (by intro c w hw; exact clean_emitRow _ w hw)
    cs regs (baseWork [] row factor) rest (clean_base [] row factor)
  rw [fold_emitRow] at h
  exact ⟨n,rf,hn,h⟩

/-- Each row's actual coordinate calls run in list order. Framing adds one
list terminator after all coordinate packets and preserves the factor buffer. -/
theorem rowBody_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p)
    (hc : SubexpBlueprintCoordinate.ContextGood ctx source target minusOne point)
    (r : Row p D) (regs : Fin 8 → Bool) (rest factor : Bits) :
    ∃ n rf, n ≤ cost ctx source target minusOne point r ∧
      Eval rowBody n (state ctx regs (baseWork (encode r ++ rest) [] factor))
        (state ctx rf (baseWork rest []
          ((record (SubexpTableSource.encodeRow (output ctx source target minusOne point r))).reverse ++ factor))) := by
  let input := Encoding.encodeList SubexpBlueprintCoordinate.encode r.coordinates ++ rest
  let rowBits := Encoding.frame r.value
  let rs := coordinateRecords ctx source target minusOne point r.coordinates
  let w0 := baseWork (Encoding.frame r.value ++ input) [] factor
  have hcapture := capture_field ctx regs w0 .payload (by decide) (by decide)
    r.value input rfl rfl rfl
  let r1 := readRegs regs 0 1 none
  let w1 : Work := {input:=input,payload:=r.value,factor:=factor}
  have hframe := appendFrame_field ctx r1 w1 .payload .row
    (by decide) (by decide) (by decide) rfl
  let r2 := afterFrameRegs r1
  let w2 : Work := {w1 with row:=rowBits.reverse}
  change Eval (appendFrame 107 111) (8*r.value.length+7) (state ctx r1 w1)
    (state ctx r2 {w1 with row:=rowBits.reverse ++ []}) at hframe
  simp only [List.append_nil] at hframe
  have hclear := clear_field ctx r2 w2 .payload
  let r3 := readRegs r2 0 1 none
  obtain ⟨ns,r4,hns,hscan⟩ := coordinates_eval ctx source target minusOne point hc
    r.coordinates r3 rest rowBits.reverse factor
  let w3 := baseWork rest (rs.reverse ++ rowBits.reverse) factor
  have hclose := closeList_field ctx r4 w3 .row .factor
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
  have hrow : (false :: (rs.reverse ++ rowBits.reverse)).reverse =
      SubexpTableSource.encodeRow (output ctx source target minusOne point r) := by
    simp only [List.reverse_cons,List.reverse_append,List.reverse_reverse,
      SubexpTableSource.encodeRow,output,encodeList_eq_records,
      List.map_map,Function.comp_def]
    rw [List.append_assoc]
    rfl
  change Eval (closeList 111 112) (13*(rs.reverse ++ rowBits.reverse).length+30)
    (state ctx r4 w3)
    (state ctx (afterFrameRegs r4) (baseWork rest []
      ((record (false :: (rs.reverse ++ rowBits.reverse)).reverse).reverse ++ factor))) at hclose
  rw [hrow] at hclose
  have h := hcapture.seq (hframe.seq (hclear.seq (hscan.seq hclose)))
  refine ⟨_,afterFrameRegs r4,?_,by
    simpa only [rowBody,inputState,baseWork,put,fieldValue,Field.port,w0,w1,w2,w3,
      input,rowBits,rs,encode_eq,List.append_assoc] using h⟩
  simp only [List.length_append,List.length_reverse]
  dsimp only [cost]
  simp only [List.length_append]
  omega

def rowsOutput (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (rows : List (Row p D)) : List SubexpTableSource.Row :=
  rows.map (output ctx source target minusOne point)

def rowsCost (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p) (rows : List (Row p D)) : ℕ :=
  scanBudget encode (cost ctx source target minusOne point) rows+
    3*(SubexpTableSource.encodeRows (rowsOutput ctx source target minusOne point rows)).length+7

/-- The full raw-row loop builds every Ce literal and returns forward row
bytes, with all coordinate, row, and factor buffers empty again. -/
theorem rawRows_eval (ctx : Context) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p (D+1)))
    (point : Fin D → ResidueCode p)
    (hc : SubexpBlueprintCoordinate.ContextGood ctx source target minusOne point)
    (rows : List (Row p D)) (regs : Fin 8 → Bool) :
    ∃ n rf, n ≤ rowsCost ctx source target minusOne point rows ∧
      Eval rawRows n
        (serviceState ctx regs (Subexp.FactorBlueprint.encodeRows (rows.map Row.packet)))
        (serviceState ctx rf
          (SubexpTableSource.encodeRows (rowsOutput ctx source target minusOne point rows))) := by
  let enc := fun r => record (SubexpTableSource.encodeRow
    (output ctx source target minusOne point r))
  let records := (rows.map enc).flatten
  let Inv := fun w : Work => Clean w ∧ w.row = []
  obtain ⟨ns,rs,hns,hs⟩ := scan_work ctx rowBody encode
    (cost ctx source target minusOne point) (fun r w => emitFactor (enc r) w) Inv
    (by intro w hw; rw [show w = baseWork w.input w.row w.factor from hw.1]; rfl)
    (by
      intro r rr w tail hw
      obtain ⟨n,rf,hn,h⟩ := rowBody_eval ctx source target minusOne point hc r rr tail w.factor
      refine ⟨n,rf,hn,?_⟩
      have hw' : w = baseWork w.input w.row w.factor := hw.1
      have hs := congrArg (fun z => inputState ctx rr z (encode r ++ tail)) hw'
      have he := congrArg (fun z => inputState ctx rf (emitFactor (enc r) z) tail) hw'
      rw [hs,he]
      simpa only [inputState,hw.2,emitFactor,enc,baseWork] using h)
    (by
      intro r w hw
      exact ⟨clean_emitFactor _ w hw.1,hw.2⟩)
    rows regs (baseWork [] [] []) [] ⟨clean_base [] [] [],rfl⟩
  rw [fold_emitFactor] at hs
  simp only [inputState,emitFactor,baseWork,List.append_nil] at hs
  let w1 := baseWork [] [] records.reverse
  have hp := push_field ctx rs w1 .factor false
  let rp := Function.update rs 0 false
  let w2 := baseWork [] [] (false :: records.reverse)
  have ht := transfer_field ctx rp w2 .factor .input (by decide)
  have hbytes : (false :: records.reverse).reverse =
      SubexpTableSource.encodeRows (rowsOutput ctx source target minusOne point rows) := by
    simp only [SubexpTableSource.encodeRows,rowsOutput,encodeList_eq_records,
      List.reverse_cons,List.reverse_reverse,List.map_map,Function.comp_def]
    rfl
  change Eval (transfer 112 100) (3*(false :: records.reverse).length+3) (state ctx rp w2)
    (state ctx (readRegs rp 0 1 none) (baseWork ((false :: records.reverse).reverse ++ []) [] [])) at ht
  rw [hbytes,List.append_nil] at ht
  have h := hs.seq (hp.seq ht)
  refine ⟨_,readRegs rp 0 1 none,?_,by
    simpa only [rawRows,serviceState,encodeRows_eq,
      inputState,emitFactor,baseWork,put,fieldValue,Field.port,w1,w2,records,enc,
      List.append_nil] using h⟩
  have hlen := congrArg List.length hbytes
  simp only [List.length_reverse,List.length_cons] at hlen
  change ns + (2 + (3*(false :: records.reverse).length+3)) ≤
    scanBudget encode (cost ctx source target minusOne point) rows +
      3*(SubexpTableSource.encodeRows (rowsOutput ctx source target minusOne point rows)).length+7
  rw [←hlen]
  simp only [List.length_cons,List.length_reverse]
  omega

end SubexponentialSAT.SubexpBlueprintRows

end OAI.Algorithms
