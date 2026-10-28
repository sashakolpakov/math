import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCacheArgumentState

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpCacheArgument

open BitProgram StructuredCalls SubexpScanPrimitives

private theorem ready_stacks_regs (regs regs' : Fin 8 → Bool) (I : Inputs)
    (output outer outerPayload inner innerPayload : List Bool) (i right j : ℕ) :
    (ready regs I output outer outerPayload inner innerPayload i right j).stacks =
      (ready regs' I output outer outerPayload inner innerPayload i right j).stacks := rfl

@[simp] theorem read_work (v p mark u saved tag present spare : Bool) (top : Option Bool) :
    readRegs (flags v p mark u saved tag present spare) 0 1 top =
      flags (top.getD false) top.isSome mark u saved tag present spare := by
  simp only [readRegs,update_flags_0,update_flags_1]

@[simp] theorem read_control (v p mark u saved tag present spare : Bool) (top : Option Bool) :
    readRegs (flags v p mark u saved tag present spare) 5 6 top =
      flags v p mark u saved (top.getD false) top.isSome spare := by
  simp only [readRegs,update_flags_5,update_flags_6]

@[simp] theorem inner_state (v p mark u saved tag present spare nt np ns : Bool) (I : Inputs)
    (output outer outerPayload inner innerPayload source payload : List Bool) (i right j : ℕ) :
    RecordPrograms.state innerPorts
      (ready (flags v p mark u saved tag present spare) I output outer outerPayload inner innerPayload i right j)
      nt np ns source payload =
      ready (flags v p mark u saved nt np ns) I output outer outerPayload source payload i right j := by
  apply state_ext
  · change Function.update (Function.update (Function.update
      (flags v p mark u saved tag present spare) 5 nt) 6 np) 7 ns = _
    simp only [update_flags_5,update_flags_6,update_flags_7,ready,machine_regs]
  · change Function.update (Function.update
      (machine (flags v p mark u saved tag present spare) I output outer outerPayload
        inner innerPayload i right j [] [] 0 0 0 0).stacks 8 source) 9 payload = _
    rw [machine_update_8,machine_update_9]
    exact ready_stacks_regs _ _ I output outer outerPayload source payload i right j

@[simp] theorem outer_state (v p mark u saved tag present spare nt np ns : Bool) (I : Inputs)
    (output outer outerPayload inner innerPayload source payload : List Bool) (i right j : ℕ) :
    RecordPrograms.state outerPorts
      (ready (flags v p mark u saved tag present spare) I output outer outerPayload inner innerPayload i right j)
      nt np ns source payload =
      ready (flags v p mark u saved nt np ns) I output source payload inner innerPayload i right j := by
  apply state_ext
  · change Function.update (Function.update (Function.update
      (flags v p mark u saved tag present spare) 5 nt) 6 np) 7 ns = _
    simp only [update_flags_5,update_flags_6,update_flags_7,ready,machine_regs]
  · change Function.update (Function.update
      (machine (flags v p mark u saved tag present spare) I output outer outerPayload
        inner innerPayload i right j [] [] 0 0 0 0).stacks 6 source) 7 payload = _
    rw [machine_update_6,machine_update_7]
    exact ready_stacks_regs _ _ I output source payload inner innerPayload i right j

theorem reader_inner (v p mark u saved tag present spare : Bool) (I : Inputs)
    (output outer outerPayload bits tail : List Bool) (i right j : ℕ) :
    Eval (RecordPrograms.reader innerPorts) (6*bits.length+4)
      (ready (flags v p mark u saved tag present spare) I output outer outerPayload
        (Encoding.frame bits ++ tail) [] i right j)
      (ready (flags v p mark u saved false true spare) I output outer outerPayload
        tail bits.reverse i right j) := by
  have h := RecordPrograms.reader_eval innerPorts
    (ready (flags v p mark u saved tag present spare) I output outer outerPayload [] [] i right j)
    bits tail [] tag present spare
  simpa only [inner_state,List.append_nil] using h

theorem reader_outer (v p mark u saved tag present spare : Bool) (I : Inputs)
    (output inner innerPayload bits tail : List Bool) (i right j : ℕ) :
    Eval (RecordPrograms.reader outerPorts) (6*bits.length+4)
      (ready (flags v p mark u saved tag present spare) I output
        (Encoding.frame bits ++ tail) [] inner innerPayload i right j)
      (ready (flags v p mark u saved false true spare) I output
        tail bits.reverse inner innerPayload i right j) := by
  have h := RecordPrograms.reader_eval outerPorts
    (ready (flags v p mark u saved tag present spare) I output [] [] inner innerPayload i right j)
    bits tail [] tag present spare
  simpa only [outer_state,List.append_nil] using h

def hasItems {α : Type*} : List α → Bool | [] => false | _::_ => true

def pending (records : List (List Bool)) (tail : List Bool) : List Bool :=
  match records with
  | [] => tail
  | c::cs => Encoding.frame c ++ (Encoding.encodeList id cs ++ tail)

theorem pop_inner_list (v p mark u saved tag present spare : Bool) (I : Inputs)
    (output outer outerPayload tail : List Bool) (records : List (List Bool)) (i right j : ℕ) :
    Eval (atom (.pop 8 5 6)) 1
      (ready (flags v p mark u saved tag present spare) I output outer outerPayload
        (Encoding.encodeList id records ++ tail) [] i right j)
      (ready (flags v p mark u saved (hasItems records) true spare) I output outer outerPayload
        (pending records tail) [] i right j) := by
  cases records with
  | nil =>
    simpa only [ready,Encoding.encodeList,pending,hasItems,read_control,
      Option.getD_some,Option.isSome_some,List.cons_append,List.nil_append,List.append_assoc,
      id_eq] using
      pop_inner (flags v p mark u saved tag present spare) I output outer outerPayload [] []
        i right j [] [] 0 0 0 0 false tail
  | cons c cs =>
    simpa only [ready,Encoding.encodeList,pending,hasItems,read_control,
      Option.getD_some,Option.isSome_some,List.cons_append,List.nil_append,List.append_assoc,
      id_eq] using
      pop_inner (flags v p mark u saved tag present spare) I output outer outerPayload [] []
        i right j [] [] 0 0 0 0 true (Encoding.frame c ++ (Encoding.encodeList id cs ++ tail))

theorem pop_outer_list (v p mark u saved tag present spare : Bool) (I : Inputs)
    (output inner innerPayload tail : List Bool) (records : List (List Bool)) (i right j : ℕ) :
    Eval (atom (.pop 6 5 6)) 1
      (ready (flags v p mark u saved tag present spare) I output
        (Encoding.encodeList id records ++ tail) [] inner innerPayload i right j)
      (ready (flags v p mark u saved (hasItems records) true spare) I output
        (pending records tail) [] inner innerPayload i right j) := by
  cases records with
  | nil =>
    simpa only [ready,Encoding.encodeList,pending,hasItems,read_control,
      Option.getD_some,Option.isSome_some,List.cons_append,List.nil_append,List.append_assoc] using
      pop_outer (flags v p mark u saved tag present spare) I output [] [] inner innerPayload
        i right j [] [] 0 0 0 0 false tail
  | cons c cs =>
    simpa only [ready,Encoding.encodeList,pending,hasItems,read_control,
      Option.getD_some,Option.isSome_some,List.cons_append,List.nil_append,List.append_assoc,
      id_eq] using
      pop_outer (flags v p mark u saved tag present spare) I output [] [] inner innerPayload
        i right j [] [] 0 0 0 0 true (Encoding.frame c ++ (Encoding.encodeList id cs ++ tail))

end SubexponentialSAT.SubexpCacheArgument

end OAI.Algorithms
