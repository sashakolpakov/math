import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookupBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

/-- Copy and frame both runtime fields; the second is their unary concatenation. -/
theorem buildQuery_eval (regs : Fin 16 → Bool)
    (literal ambient factor master : List Bool) :
    ∃ rf, Eval buildQuery (31*(literal.length+ambient.length+factor.length)+88)
      (data regs literal ambient factor master [] [] [] [] [] [] [] [])
      (data rf literal ambient factor master [] []
        (pairKey literal (ambient++factor)) [] [] [] [] []) := by
  let r1 := readRegs regs 0 1 none
  have h1 := copy_eval (data regs literal ambient factor master [] [] [] [] [] [] [] []) 2 6 11 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have e1 : afterCopy (data regs literal ambient factor master [] [] [] [] [] [] [] []) 2 6 0 1 =
      data r1 literal ambient factor master [] [] factor [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data,afterCopy,StackRoutines.copyStacks]
  rw [e1] at h1
  let r2 := readRegs r1 0 1 none
  have h2 := copy_eval (data r1 literal ambient factor master [] [] factor [] [] [] [] []) 1 6 11 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have e2 : afterCopy (data r1 literal ambient factor master [] [] factor [] [] [] [] []) 1 6 0 1 =
      data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data,afterCopy,StackRoutines.copyStacks]
  rw [e2] at h2
  let r3 := Function.update r2 0 false
  have h3 := push_eval 5 false (data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] [])
  have e3 : (⟨Function.update (data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] []).regs 0 false,Function.update (data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] []).stacks 5
      (false::(data r2 literal ambient factor master [] [] (ambient++factor) [] [] [] [] []).stacks 5)⟩ : Data) =
      data r3 literal ambient factor master [] (false::([])) (ambient++factor) [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data]
  rw [e3] at h3
  obtain ⟨out4,h4,hs4⟩ := LayoutMatrixProgram.frame_eval 6 5 7
    (by decide) (by decide) (by decide) (data r3 literal ambient factor master [] (false::([])) (ambient++factor) [] [] [] [] []) rfl
  let r4 := out4.regs
  have e4 : out4 = data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · rw [hs4]
      funext i; fin_cases i <;>
        simp [data]
  rw [e4] at h4
  let r5 := Function.update r4 0 true
  have h5 := push_eval 5 true (data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] [])
  have e5 : (⟨Function.update (data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] []).regs 0 true,Function.update (data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] []).stacks 5
      (true::(data r4 literal ambient factor master [] (Encoding.frame (ambient++factor)++(false::([]))) [] [] [] [] [] []).stacks 5)⟩ : Data) =
      data r5 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data]
  rw [e5] at h5
  let r6 := readRegs r5 0 1 none
  have h6 := copy_eval (data r5 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) [] [] [] [] [] []) 0 6 11 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  have e6 : afterCopy (data r5 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) [] [] [] [] [] []) 0 6 0 1 =
      data r6 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) literal [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data,afterCopy,StackRoutines.copyStacks]
  rw [e6] at h6
  obtain ⟨out7,h7,hs7⟩ := LayoutMatrixProgram.frame_eval 6 5 7
    (by decide) (by decide) (by decide) (data r6 literal ambient factor master [] (true::(Encoding.frame (ambient++factor)++(false::([])))) literal [] [] [] [] []) rfl
  let r7 := out7.regs
  have e7 : out7 = data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · rw [hs7]
      funext i; fin_cases i <;>
        simp [data]
  rw [e7] at h7
  let r8 := Function.update r7 0 true
  have h8 := push_eval 5 true (data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] [])
  have e8 : (⟨Function.update (data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] []).regs 0 true,Function.update (data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] []).stacks 5
      (true::(data r7 literal ambient factor master [] (Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([]))))) [] [] [] [] [] []).stacks 5)⟩ : Data) =
      data r8 literal ambient factor master [] (true::(Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([])))))) [] [] [] [] [] [] := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [data]
  rw [e8] at h8
  obtain ⟨out9,h9,hs9⟩ := LayoutMatrixProgram.frame_eval 5 6 7
    (by decide) (by decide) (by decide) (data r8 literal ambient factor master [] (true::(Encoding.frame (literal)++(true::(Encoding.frame (ambient++factor)++(false::([])))))) [] [] [] [] [] []) rfl
  let r9 := out9.regs
  have e9 : out9 = data r9 literal ambient factor master [] [] (pairKey literal (ambient++factor)) [] [] [] [] [] := by
    apply state_ext
    · rfl
    · rw [hs9]
      funext i; fin_cases i <;>
        simp [data,pairKey,ProgramEncoding.encodeRecords,Encoding.encodeList]
  rw [e9] at h9
  refine ⟨r9,?_⟩
  have hh := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq (h9))))))))
  convert hh using 1 <;>
    simp [buildQuery,copy,data,Encoding.length_frame] ; omega

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
