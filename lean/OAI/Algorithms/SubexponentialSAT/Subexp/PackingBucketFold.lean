import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable

namespace OAI.Algorithms

/-! Measured execution of the physical all-key packing fold. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls MatrixProgramSupport PackingBucketCalls

def finishRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update regs 5 false) 6 true) 7 false

def afterBucket (records : List BucketProgram.Record) (query acc : List Bool) : List Bool :=
  (true :: Encoding.frame (bucketPayload records query)).reverse ++ acc

theorem callback_eval (records : List BucketProgram.Record) (query tail acc : List Bool)
    (m : ℕ) (hm : m ≤ records.length) (regs : Fin 8 → Bool) :
    ∃ n ≤ callbackCost records query, ∃ rf,
      Eval callback n
        (state regs [] query.reverse [] (BucketProgram.encodeRecords records.reverse)
          tail [] (List.replicate m true) acc [] [])
        (state (finishRegs rf) [] [] [] (BucketProgram.encodeRecords records.reverse)
          tail [] (List.replicate (min m (BucketProgram.selected records query).length) true)
          (afterBucket records query acc) [] []) := by
  let items := BucketProgram.selected records query
  let bytes := words items
  let saved := BucketProgram.encodeRecords records.reverse
  let k := min m items.length
  let record := bucketPayload records query
  let recordBits := true :: Encoding.frame record
  obtain ⟨d1, h1, hs1⟩ := MatrixProgramSupport.copy_eval (6 : Fin 15) 0 12
    (by decide) (by decide) (by decide)
    (state regs [] query.reverse [] saved tail [] (List.replicate m true) acc [] []) rfl
  have hd1 : d1 = state d1.regs saved query.reverse [] saved tail []
      (List.replicate m true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs1]
    funext j
    fin_cases j <;> simp [state, StackRoutines.copyStacks]
  rw [hd1] at h1
  obtain ⟨n2, hn2, r2, h2⟩ := bucketCall_eval records query d1.regs
    saved tail [] (List.replicate m true) acc [] []
  change Eval bucketCall n2
    (state d1.regs saved query.reverse [] saved tail [] (List.replicate m true) acc [] [])
    (state r2 [] query.reverse bytes saved tail [] (List.replicate m true) acc [] []) at h2
  obtain ⟨d3, h3, hs3⟩ := MatrixProgramSupport.copy_eval (5 : Fin 15) 9 12
    (by decide) (by decide) (by decide)
    (state r2 [] query.reverse bytes saved tail [] (List.replicate m true) acc [] []) rfl
  have hd3 : d3 = state d3.regs [] query.reverse bytes saved tail bytes
      (List.replicate m true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs3]
    funext j
    fin_cases j <;> simp [state, StackRoutines.copyStacks]
  rw [hd3] at h3
  obtain ⟨n4, hn4, r4, h4⟩ := countCall_eval items d3.regs
    [] query.reverse bytes saved tail (List.replicate m true) acc []
  obtain ⟨n5, hn5, r5, h5⟩ := minimumCall_eval m items.length r4
    [] query.reverse bytes saved tail [] acc
  obtain ⟨d6, h6, hs6⟩ := move_eval (14 : Fin 15) 10 12
    (by decide) (by decide) (by decide)
    (state r5 [] query.reverse bytes saved tail [] [] acc [] (List.replicate k true)) rfl rfl
  have hd6 : d6 = state d6.regs [] query.reverse bytes saved tail []
      (List.replicate k true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs6]
    funext j
    fin_cases j <;> simp [state]
  rw [hd6] at h6
  obtain ⟨d7, h7, hs7⟩ := transfer_eval (2 : Fin 15) 9 (by decide)
    (state d6.regs [] query.reverse bytes saved tail [] (List.replicate k true) acc [] [])
  have hd7 : d7 = state d7.regs [] [] bytes saved tail query
      (List.replicate k true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs7]
    funext j
    fin_cases j <;> simp [state, StackRoutines.transferStacks]
  rw [hd7] at h7
  obtain ⟨d8, h8, hs8⟩ := emitFrame_eval (9 : Fin 15) 5 12
    (by decide) (by decide) (by decide)
    (state d7.regs [] [] bytes saved tail query (List.replicate k true) acc [] []) rfl
  have hd8 : d8 = state d8.regs [] [] record saved tail []
      (List.replicate k true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs8]
    funext j
    fin_cases j <;> simp [state, record, bucketPayload, bytes, items]
  rw [hd8] at h8
  obtain ⟨d9, h9, hs9⟩ := emitFrame_eval (5 : Fin 15) 9 12
    (by decide) (by decide) (by decide)
    (state d8.regs [] [] record saved tail [] (List.replicate k true) acc [] []) rfl
  have hd9 : d9 = state d9.regs [] [] [] saved tail (Encoding.frame record)
      (List.replicate k true) acc [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs9]
    funext j
    fin_cases j <;> simp [state]
  rw [hd9] at h9
  let r10 := Function.update d9.regs (0 : Fin 8) true
  have h10 : Eval (TupleProgram.pushConst 9 0 true) 2
      (state d9.regs [] [] [] saved tail (Encoding.frame record) (List.replicate k true) acc [] [])
      (state r10 [] [] [] saved tail recordBits (List.replicate k true) acc [] []) := by
    have ht := TupleProgram.pushConst_eval (9 : Fin 15) (0 : Fin 8) true
      (state d9.regs [] [] [] saved tail (Encoding.frame record) (List.replicate k true) acc [] [])
    have hf : TupleProgram.pushedState 9 0 true
        (state d9.regs [] [] [] saved tail (Encoding.frame record) (List.replicate k true) acc [] []) =
        state r10 [] [] [] saved tail recordBits (List.replicate k true) acc [] [] := by
      apply MatrixProgramSupport.data_ext <;> try rfl
      funext j
      fin_cases j <;> rfl
    rw [hf] at ht
    exact ht
  obtain ⟨d11, h11, hs11⟩ := transfer_eval (9 : Fin 15) 11 (by decide)
    (state r10 [] [] [] saved tail recordBits (List.replicate k true) acc [] [])
  have hd11 : d11 = state d11.regs [] [] [] saved tail []
      (List.replicate k true) (recordBits.reverse ++ acc) [] [] := by
    apply MatrixProgramSupport.data_ext <;> try rfl
    rw [hs11]
    funext j
    fin_cases j <;> simp [state, StackRoutines.transferStacks]
  rw [hd11] at h11
  have h12 : Eval (sequence [.base (.atom (.set 5 false)),
      .base (.atom (.set 6 true)), .base (.atom (.set 7 false))]) 3
      (state d11.regs [] [] [] saved tail [] (List.replicate k true) (recordBits.reverse ++ acc) [] [])
      (state (finishRegs d11.regs) [] [] [] saved tail []
        (List.replicate k true) (recordBits.reverse ++ acc) [] []) := by
    exact (Eval.base (.atom _ _)).seq ((Eval.base (.atom _ _)).seq
      ((Eval.base (.atom _ _)).seq (Eval.base (.skip _))))
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq
    (h7.seq (h8.seq (h9.seq (h10.seq (h11.seq h12))))))))))
  let total := (7 * saved.length + 5) + (n2 + ((7 * bytes.length + 5) +
    (n4 + (n5 + ((6 * k + 6) + ((3 * query.length + 3) + ((8 * query.length + 8) +
      ((8 * record.length + 8) + (2 + ((3 * recordBits.length + 3) + 3))))))))))
  refine ⟨total, ?_, d11.regs, ?_⟩
  · have hlen := BucketProgram.record_count_le_length records
    have hnlen := (selected_length_le records query).trans hlen
    have hblen := selected_words_length_le records query
    have hb := BucketProgram.loopBudget_le records.reverse query
    rw [encodeRecords_length_reverse, List.length_reverse] at hb
    have hmul := Nat.mul_le_mul_right (9 * query.length + 20) hlen
    have hscan : n2 ≤ 9 * (BucketProgram.encodeRecords records).length +
        (BucketProgram.encodeRecords records).length * (9 * query.length + 20) + 3 := by
      omega
    have hbound := callback_arithmetic (BucketProgram.encodeRecords records).length
      query.length m items.length bytes.length n2 (hm.trans hlen) hnlen hblen hscan
    have hrecord : record.length = 2 * query.length + 1 + bytes.length := by
      simp [record, bucketPayload, bytes, items, Encoding.length_frame]
    have hrecordBits : recordBits.length = 2 * record.length + 2 := by
      simp only [recordBits, List.length_cons, Encoding.length_frame]
    dsimp only [callbackCost, total, k]
    simp only [show saved.length = (BucketProgram.encodeRecords records).length from
      encodeRecords_length_reverse records, hrecordBits, hrecord]
    dsimp only [bytes, items] at hn4 hn5 hbound ⊢
    omega
  · simpa [callback, sequence, total, state, saved, k, recordBits, record,
      afterBucket, bytes, items, List.length_replicate, Encoding.length_frame] using he

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
