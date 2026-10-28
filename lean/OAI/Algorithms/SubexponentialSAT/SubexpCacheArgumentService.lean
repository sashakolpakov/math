import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCacheArgumentState

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpCacheArgument

open BitProgram StructuredCalls SubexpScanPrimitives

theorem serviceRegs_injective : Function.Injective serviceRegs := by
  intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 8 => x.val) h

theorem servicePorts_injective : Function.Injective servicePorts := by decide

def prepend (left right j B : ℕ) (mark u : Bool) (c output : List Bool) : List Bool :=
  true :: (Encoding.frame (SubexpArgumentProgram.recordBody
    (SubexpArgumentKeyEmitter.paddedKey left right j B mark u) c) ++ output)

theorem prepared_eval (regs : Fin 8 → Bool) (I : Inputs)
    (output outer outerPayload inner innerPayload : List Bool)
    (i right j : ℕ) (c : List Bool) (left keyRight z : ℕ) :
    Eval emitPrepared
      (SubexpRawArgumentService.cost left keyRight z I.keyWidth (regs 2) (regs 3) c + 1)
      (machine regs I output outer outerPayload inner innerPayload i right j c []
        left keyRight z I.keyWidth)
      (ready (finish regs) I (prepend left keyRight z I.keyWidth (regs 2) (regs 3) c output)
        outer outerPayload inner innerPayload i right j) := by
  let rr := fun k => regs (serviceRegs k)
  let a := SubexpRawArgumentService.state rr c [] (unary left) output
    (unary keyRight) (unary z) (unary I.keyWidth) []
  let b := SubexpRawArgumentService.state (SubexpArgumentProgram.finishedRegs rr) [] [] []
    (prepend left keyRight z I.keyWidth (regs 2) (regs 3) c output) [] [] [] []
  let start := machine regs I output outer outerPayload inner innerPayload i right j c []
    left keyRight z I.keyWidth
  let stop := ready (finish regs) I (prepend left keyRight z I.keyWidth (regs 2) (regs 3) c output)
    outer outerPayload inner innerPayload i right j
  have ha : embedState serviceRegs servicePorts start a = start := by
    apply embedState_eq _ _ serviceRegs_injective servicePorts_injective
    · intros; rfl
    · intro k; fin_cases k <;>
        simp [a,start,SubexpRawArgumentService.state,servicePorts]
    · intros; rfl
    · intros; rfl
  have hb : embedState serviceRegs servicePorts start b = stop := by
    apply embedState_eq _ _ serviceRegs_injective servicePorts_injective
    · intro k; fin_cases k <;> rfl
    · intro k; fin_cases k <;>
        simp [b,stop,ready,SubexpRawArgumentService.state,servicePorts]
    · intro k hk
      have h0 : k ≠ 0 := fun h => hk ⟨0,h.symm⟩
      have h1 : k ≠ 1 := fun h => hk ⟨1,h.symm⟩
      simp [start,stop,ready,finish,h0,h1]
    · intro k hk
      have h5 : k ≠ 5 := fun h => hk ⟨3,h.symm⟩
      have h14 : k ≠ 14 := fun h => hk ⟨2,h.symm⟩
      have h15 : k ≠ 15 := fun h => hk ⟨4,h.symm⟩
      have h16 : k ≠ 16 := fun h => hk ⟨5,h.symm⟩
      have h17 : k ≠ 17 := fun h => hk ⟨6,h.symm⟩
      have h19 : k ≠ 19 := fun h => hk ⟨0,h.symm⟩
      fin_cases k <;> first | contradiction | simp [start,stop,ready]
  have h := eval_call_lifted SubexpRawArgumentService.program serviceRegs servicePorts start
    serviceRegs_injective servicePorts_injective
    (SubexpRawArgumentService.program_trace left keyRight z I.keyWidth rr c output [])
  change Eval emitPrepared _ (embedState serviceRegs servicePorts start a)
    (embedState serviceRegs servicePorts start b) at h
  rw [ha,hb] at h
  exact h

def variableCost (i right j B : ℕ) (mark u : Bool) (c : List Bool) : ℕ :=
  (3*c.length+3) + ((7*i+5) + ((7*right+5) + ((7*j+5) + ((7*B+5) +
    (SubexpRawArgumentService.cost i right j B mark u c + 1)))))

theorem variable_eval (regs : Fin 8 → Bool) (I : Inputs)
    (output outer outerPayload inner : List Bool) (i right j : ℕ) (c : List Bool) :
    Eval emitVariable (variableCost i right j I.keyWidth (regs 2) (regs 3) c)
      (ready regs I output outer outerPayload inner c.reverse i right j)
      (ready (finish regs) I (prepend i right j I.keyWidth (regs 2) (regs 3) c output)
        outer outerPayload inner [] i right j) := by
  have h1 := transfer_9_19 regs I output outer outerPayload inner [] i right j [] [] 0 0 0 0 c
  have h2 := copy_10_14 (reset regs) I output outer outerPayload inner [] i right j c [] 0 0 0 0
  have h3 := copy_11_15 (reset regs) I output outer outerPayload inner [] i right j c [] i 0 0 0
  have h4 := copy_12_16 (reset regs) I output outer outerPayload inner [] i right j c [] i right 0 0
  have h5 := copy_4_17 (reset regs) I output outer outerPayload inner [] i right j c [] i right j 0
  have h6 := prepared_eval (reset regs) I output outer outerPayload inner [] i right j c i right j
  simp only [reset_reset] at h2 h3 h4 h5
  have hr2 : reset regs 2 = regs 2 := by simp [reset,readRegs]
  have hr3 : reset regs 3 = regs 3 := by simp [reset,readRegs]
  simp only [hr2,hr3,finish_reset] at h6
  exact h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))

end SubexponentialSAT.SubexpCacheArgument

end OAI.Algorithms
