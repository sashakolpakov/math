import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCacheArgumentService
import OAI.Algorithms.SubexponentialSAT.SubexpCacheArgumentReader

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpCacheArgument

open BitProgram StructuredCalls

abbrev Bits := List Bool

def innerOutput (i right j B : ℕ) (u : Bool) : List Bits → Bits → Bits
  | [], output => output
  | c::cs, output => innerOutput i right (j+1) B false cs
      (prepend i right j B true u c output)

def innerCost (i right j B : ℕ) (u : Bool) : List Bits → ℕ
  | [] => 1
  | c::cs => (6*c.length+4 + (variableCost i right j B true u c + (2+(1+1)))) +
      innerCost i right (j+1) B false cs + 1

theorem innerBody_eval (v p u saved spare : Bool) (I : Inputs)
    (output outer outerPayload c tail : Bits) (cs : List Bits) (i right j : ℕ) :
    Eval innerBody (6*c.length+4 + (variableCost i right j I.keyWidth true u c + (2+(1+1))))
      (ready (flags v p true u saved true true spare) I output outer outerPayload
        (Encoding.frame c ++ (Encoding.encodeList id cs ++ tail)) [] i right j)
      (ready (flags true false true false saved (hasItems cs) true spare) I
        (prepend i right j I.keyWidth true u c output) outer outerPayload
        (pending cs tail) [] i right (j+1)) := by
  let output' := prepend i right j I.keyWidth true u c output
  let tail' := Encoding.encodeList id cs ++ tail
  have h1 := reader_inner v p true u saved true true spare I output outer outerPayload c tail' i right j
  have h2 := variable_eval (flags v p true u saved false true spare) I output outer outerPayload tail' i right j c
  simp only [flags_2,flags_3,finish_flags] at h2
  have h3 := push_j (flags true false true u saved false true spare) I output' outer outerPayload tail' []
    i right j [] [] 0 0 0 0
  simp only [update_flags_0] at h3
  have h4 := set_machine (flags true false true u saved false true spare) I output' outer outerPayload tail' []
    i right (j+1) [] [] 0 0 0 0 3 false
  simp only [update_flags_3] at h4
  have h5 := pop_inner_list true false true false saved false true spare I output' outer outerPayload tail cs i right (j+1)
  exact h1.seq (h2.seq (h3.seq (h4.seq h5)))

theorem innerLoop_eval (cs : List Bits) (v p u saved spare : Bool) (I : Inputs)
    (output outer outerPayload tail : Bits) (i right j : ℕ) :
    ∃ vf pf, Eval innerLoop (innerCost i right j I.keyWidth u cs)
      (ready (flags v p true u saved (hasItems cs) true spare) I output outer outerPayload
        (pending cs tail) [] i right j)
      (ready (flags vf pf true (if cs=[] then u else false) saved false true spare) I
        (innerOutput i right j I.keyWidth u cs output) outer outerPayload tail [] i right (j+cs.length)) := by
  induction cs generalizing v p u output j with
  | nil =>
    refine ⟨v,p,?_⟩
    simpa [innerCost,innerOutput,pending,hasItems] using
      (Eval.while_false (test := (5 : Fin 8)) (body := innerBody)
        (a := ready (flags v p true u saved false true spare) I output outer outerPayload tail [] i right j) rfl)
  | cons c cs ih =>
    have hb := innerBody_eval v p u saved spare I output outer outerPayload c tail cs i right j
    obtain ⟨vf,pf,hr⟩ := ih true false false (output := prepend i right j I.keyWidth true u c output) (j := j+1)
    refine ⟨vf,pf,?_⟩
    have h := Eval.while_true (test := (5 : Fin 8)) rfl hb hr
    simpa [innerLoop,innerCost,innerOutput,pending,hasItems,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem innerRun_eval (cs : List Bits) (v p u saved tag present spare : Bool) (I : Inputs)
    (output outer outerPayload tail : Bits) (i right j : ℕ) :
    ∃ vf pf, Eval innerRun (1+innerCost i right j I.keyWidth u cs)
      (ready (flags v p true u saved tag present spare) I output outer outerPayload
        (Encoding.encodeList id cs ++ tail) [] i right j)
      (ready (flags vf pf true (if cs=[] then u else false) saved false true spare) I
        (innerOutput i right j I.keyWidth u cs output) outer outerPayload tail [] i right (j+cs.length)) := by
  have hp := pop_inner_list v p true u saved tag present spare I output outer outerPayload tail cs i right j
  obtain ⟨vf,pf,hr⟩ := innerLoop_eval cs v p u saved spare I output outer outerPayload tail i right j
  exact ⟨vf,pf,hp.seq hr⟩

def columnRecords (columns : List (List Bits)) : List Bits := columns.map (Encoding.encodeList id)

def outerOutput (i B : ℕ) : List (List Bits) → Bits → Bits
  | [], output => output
  | cs::columns, output => outerOutput (i+1) B columns
      (innerOutput i columns.length 0 B true cs output)

def outerCost (i B : ℕ) : List (List Bits) → ℕ
  | [] => 1
  | cs::columns =>
    (6*(Encoding.encodeList id cs).length+4 +
      (3*(Encoding.encodeList id cs).length+3 +
        (1 + ((1+innerCost i columns.length 0 B true cs) +
          ((2*cs.length+3) + (2+(1+1))))))) + outerCost (i+1) B columns + 1

theorem outerBody_eval (v p u saved spare : Bool) (I : Inputs)
    (output tail : Bits) (cs : List Bits) (columns : List (List Bits)) (i : ℕ) :
    ∃ vf pf, Eval outerBody
      (6*(Encoding.encodeList id cs).length+4 +
        (3*(Encoding.encodeList id cs).length+3 +
          (1 + ((1+innerCost i columns.length 0 I.keyWidth true cs) +
            ((2*cs.length+3) + (2+(1+1)))))))
      (ready (flags v p true u saved true true spare) I output
        (Encoding.frame (Encoding.encodeList id cs) ++ (Encoding.encodeList id (columnRecords columns) ++ tail))
        [] [] [] i columns.length 0)
      (ready (flags vf pf true (if cs=[] then true else false) saved (hasItems columns) true spare) I
        (innerOutput i columns.length 0 I.keyWidth true cs output)
        (pending (columnRecords columns) tail) [] [] [] (i+1) (columns.length-1) 0) := by
  let bits := Encoding.encodeList id cs
  let tail' := Encoding.encodeList id (columnRecords columns) ++ tail
  let output' := innerOutput i columns.length 0 I.keyWidth true cs output
  have h1 := reader_outer v p true u saved true true spare I output [] [] bits tail' i columns.length 0
  have h2 := transfer_7_8 (flags v p true u saved false true spare) I output tail' [] [] []
    i columns.length 0 [] [] 0 0 0 0 bits
  simp only [reset_flags] at h2
  have h3 := set_machine (flags false false true u saved false true spare) I output tail' [] bits []
    i columns.length 0 [] [] 0 0 0 0 3 true
  simp only [update_flags_3] at h3
  obtain ⟨vi,pi,h4⟩ := innerRun_eval cs false false true saved false true spare I output tail' [] [] i columns.length 0
  simp only [List.append_nil,Nat.zero_add] at h4
  have h5 := clear_j (flags vi pi true (if cs=[] then true else false) saved false true spare)
    I output' tail' [] [] [] i columns.length cs.length [] [] 0 0 0 0
  simp only [reset_flags] at h5
  have h6 := push_i (flags false false true (if cs=[] then true else false) saved false true spare)
    I output' tail' [] [] [] i columns.length 0 [] [] 0 0 0 0
  simp only [update_flags_0] at h6
  have h7 := pop_right (flags true false true (if cs=[] then true else false) saved false true spare)
    I output' tail' [] [] [] (i+1) columns.length 0 [] [] 0 0 0 0
  simp only [read_work,unary_head,unary_present] at h7
  have h8 := pop_outer_list (decide (0 < columns.length)) (decide (0 < columns.length)) true
    (if cs=[] then true else false) saved false true spare I output' [] [] tail (columnRecords columns)
    (i+1) (columns.length-1) 0
  have hh : hasItems (columnRecords columns) = hasItems columns := by cases columns <;> rfl
  rw [hh] at h8
  exact ⟨_,_,h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))⟩

theorem outerLoop_eval (columns : List (List Bits)) (v p u saved spare : Bool) (I : Inputs)
    (output tail : Bits) (i : ℕ) :
    ∃ vf pf uf, Eval outerLoop (outerCost i I.keyWidth columns)
      (ready (flags v p true u saved (hasItems columns) true spare) I output
        (pending (columnRecords columns) tail) [] [] [] i (columns.length-1) 0)
      (ready (flags vf pf true uf saved false true spare) I (outerOutput i I.keyWidth columns output)
        tail [] [] [] (i+columns.length) 0 0) := by
  induction columns generalizing v p u output i with
  | nil =>
    refine ⟨v,p,u,?_⟩
    simpa [outerCost,outerOutput,columnRecords,pending,hasItems] using
      (Eval.while_false (test := (5 : Fin 8)) (body := outerBody)
        (a := ready (flags v p true u saved false true spare) I output tail [] [] [] i 0 0) rfl)
  | cons cs columns ih =>
    obtain ⟨vb,pb,hb⟩ := outerBody_eval v p u saved spare I output tail cs columns i
    obtain ⟨vf,pf,uf,hr⟩ := ih vb pb (if cs=[] then true else false)
      (output := innerOutput i columns.length 0 I.keyWidth true cs output) (i := i+1)
    refine ⟨vf,pf,uf,?_⟩
    have h := Eval.while_true (test := (5 : Fin 8)) rfl hb hr
    simpa [outerLoop,outerCost,outerOutput,columnRecords,pending,hasItems,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def constantWord (negative : Bool) (I : Inputs) : Bits := if negative then I.negative else I.beta

def constantCost (negative u : Bool) (I : Inputs) : ℕ :=
  1+(1+((7*(constantWord negative I).length+5)+((7*I.dimension+5)+((7*I.keyWidth+5)+
    (SubexpRawArgumentService.cost I.dimension 0 0 I.keyWidth false u (constantWord negative I)+1)))))

theorem constant_eval (negative u v p mark priorU saved tag present spare : Bool) (I : Inputs)
    (output outer outerPayload inner innerPayload : Bits) (i right j : ℕ) :
    Eval (emitConstant (if negative then 1 else 0) u) (constantCost negative u I)
      (ready (flags v p mark priorU saved tag present spare) I output outer outerPayload inner innerPayload i right j)
      (ready (flags true false false u saved tag present spare) I
        (prepend I.dimension 0 0 I.keyWidth false u (constantWord negative I) output)
        outer outerPayload inner innerPayload i right j) := by
  have h1 := set_machine (flags v p mark priorU saved tag present spare) I output outer outerPayload inner innerPayload
    i right j [] [] 0 0 0 0 2 false
  simp only [update_flags_2] at h1
  have h2 := set_machine (flags v p false priorU saved tag present spare) I output outer outerPayload inner innerPayload
    i right j [] [] 0 0 0 0 3 u
  simp only [update_flags_3] at h2
  have h3 : Eval (copy (if negative then 1 else 0) 19) (7*(constantWord negative I).length+5)
      (ready (flags v p false u saved tag present spare) I output outer outerPayload inner innerPayload i right j)
      (machine (flags false false false u saved tag present spare) I output outer outerPayload inner innerPayload
        i right j (constantWord negative I) [] 0 0 0 0) := by
    cases negative
    · simpa only [constantWord, Bool.false_eq_true, ite_false, ready, reset_flags] using
        copy_0_19 (flags v p false u saved tag present spare) I output outer outerPayload inner innerPayload
          i right j [] [] 0 0 0 0
    · simpa only [constantWord, ↓reduceIte, ready, reset_flags] using
        copy_1_19 (flags v p false u saved tag present spare) I output outer outerPayload inner innerPayload
          i right j [] [] 0 0 0 0
  have h4 := copy_3_14 (flags false false false u saved tag present spare) I output outer outerPayload inner innerPayload
    i right j (constantWord negative I) [] 0 0 0 0
  simp only [reset_flags] at h4
  have h5 := copy_4_17 (flags false false false u saved tag present spare) I output outer outerPayload inner innerPayload
    i right j (constantWord negative I) [] I.dimension 0 0 0
  simp only [reset_flags] at h5
  have h6 := prepared_eval (flags false false false u saved tag present spare) I output outer outerPayload inner innerPayload
    i right j (constantWord negative I) I.dimension 0 0
  simp only [flags_2,flags_3,finish_flags] at h6
  exact h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))

def cacheInputs (beta negative : Bits) (columns : List (List Bits)) (B : ℕ) : Inputs :=
  ⟨beta,negative,Encoding.encodeList id (columnRecords columns),columns.length,B⟩

def resultBits (beta negative : Bits) (columns : List (List Bits)) (B : ℕ) (output : Bits) : Bits :=
  outerOutput 0 B columns
    (prepend columns.length 0 0 B false true negative
      (prepend columns.length 0 0 B false false beta output))

def totalCost (beta negative : Bits) (columns : List (List Bits)) (B : ℕ) : ℕ :=
  let I := cacheInputs beta negative columns B
  constantCost false false I + (constantCost true true I +
    ((7*I.cache.length+5) + ((7*I.dimension+5) + (1+(1+(1+
      (outerCost 0 B columns + (2*columns.length+3))))))))

theorem command_eval (beta negative : Bits) (columns : List (List Bits)) (B : ℕ)
    (v p mark u saved tag present spare : Bool) (output : Bits) :
    ∃ vf pf uf, Eval command (totalCost beta negative columns B)
      (ready (flags v p mark u saved tag present spare) (cacheInputs beta negative columns B)
        output [] [] [] [] 0 0 0)
      (ready (flags vf pf true uf saved false true spare) (cacheInputs beta negative columns B)
        (resultBits beta negative columns B output) [] [] [] [] 0 0 0) := by
  let I := cacheInputs beta negative columns B
  let output1 := prepend columns.length 0 0 B false false beta output
  let output2 := prepend columns.length 0 0 B false true negative output1
  have h1 := constant_eval false false v p mark u saved tag present spare I output [] [] [] [] 0 0 0
  have h2 := constant_eval true true true false false false saved tag present spare I output1 [] [] [] [] 0 0 0
  have h3 := copy_2_6 (flags true false false true saved tag present spare) I output2 [] [] [] [] 0 0 0 [] [] 0 0 0 0
  simp only [reset_flags] at h3
  have h4 := copy_3_11 (flags false false false true saved tag present spare) I output2 I.cache [] [] [] 0 0 0 [] [] 0 0 0 0
  simp only [reset_flags] at h4
  have h5 := pop_right (flags false false false true saved tag present spare) I output2 I.cache [] [] []
    0 I.dimension 0 [] [] 0 0 0 0
  simp only [read_work,unary_head,unary_present] at h5
  have h6 := set_machine (flags (decide (0 < I.dimension)) (decide (0 < I.dimension)) false true saved tag present spare)
    I output2 I.cache [] [] [] 0 (I.dimension-1) 0 [] [] 0 0 0 0 2 true
  simp only [update_flags_2] at h6
  have h7 := pop_outer_list (decide (0 < I.dimension)) (decide (0 < I.dimension)) true true saved tag present spare
    I output2 [] [] [] (columnRecords columns) 0 (I.dimension-1) 0
  have hh : hasItems (columnRecords columns) = hasItems columns := by cases columns <;> rfl
  simp only [hh,List.append_nil] at h7
  obtain ⟨vo,po,uo,h8⟩ := outerLoop_eval columns (decide (0 < I.dimension)) (decide (0 < I.dimension)) true
    saved spare I output2 [] 0
  simp only [Nat.zero_add] at h8
  have h9 := clear_i (flags vo po true uo saved false true spare) I (resultBits beta negative columns B output)
    [] [] [] [] columns.length 0 0 [] [] 0 0 0 0
  simp only [reset_flags] at h9
  refine ⟨false,false,uo,?_⟩
  exact h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))

theorem program_trace (beta negative : Bits) (columns : List (List Bits)) (B : ℕ)
    (v p mark u saved tag present spare : Bool) (output : Bits) :
    ∃ vf pf uf, Trace program (totalCost beta negative columns B+1)
      ((ready (flags v p mark u saved tag present spare) (cacheInputs beta negative columns B)
        output [] [] [] [] 0 0 0).withPC (some program.entry))
      ((ready (flags vf pf true uf saved false true spare) (cacheInputs beta negative columns B)
        (resultBits beta negative columns B output) [] [] [] [] 0 0 0).withPC none) := by
  obtain ⟨vf,pf,uf,h⟩ := command_eval beta negative columns B v p mark u saved tag present spare output
  exact ⟨vf,pf,uf,compiled_halt_trace h 0 5⟩

end SubexponentialSAT.SubexpCacheArgument

end OAI.Algorithms
