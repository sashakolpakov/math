import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramInterval
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBankUnaryCopy

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

def unaryWords (w : Words) : Words :=
  Function.update (Function.update (Function.update w 51
    (List.replicate (BinaryArithmetic.toNat (w 29)) true)) 52
      (List.replicate (BinaryArithmetic.toNat (w 46)) true)) 53
        (List.replicate (BinaryArithmetic.toNat (w 50)) true)

abbrev unaryCommand : Cmd 8 77 :=
  .seq (Bank.unaryCopyCmd 29 51)
    (.seq (Bank.unaryCopyCmd 46 52) (Bank.unaryCopyCmd 50 53))

def unaryBound (v l : ℕ) : ℕ := 7*l+6+32*(v+1)*(l+1)

theorem unaryCopyBound_le (bits : List Bool) (v l : ℕ)
    (hv : BinaryArithmetic.toNat bits=v) (hl : bits.length ≤ l) :
    Serialization.unaryCopyBound bits+1 ≤ unaryBound v l := by
  rw [Serialization.unaryCopyBound_eq,hv]
  calc
    _ = 7*bits.length+6+32*(v+1)*(bits.length+1) := by omega
    _ ≤ unaryBound v l := by
      dsimp [unaryBound]
      gcongr

def unaryRuntime (m : Model) : ℕ :=
  unaryBound (m.val 29) (m.len 29)+unaryBound (m.val 46) (m.len 46)+
    unaryBound (m.val 50) (m.len 50)

theorem unary_eval (m : Model) (r : Regs) (w : Words) (hs : Shape m w)
    (h51 : w 51=[]) (h52 : w 52=[]) (h53 : w 53=[]) :
    ∃ t rf, Eval unaryCommand t (Bank.state r w) (Bank.state rf (unaryWords w)) ∧
      t ≤ unaryRuntime m := by
  obtain ⟨t1,r1,he1,ht1⟩ := Bank.unaryCopy_eval r w 29 51 (by decide) h51
  let w1 := Function.update w 51 (List.replicate (BinaryArithmetic.toNat (w 29)) true)
  obtain ⟨t2,r2,he2,ht2⟩ := Bank.unaryCopy_eval r1 w1 46 52 (by decide)
    (by simpa [w1] using h52)
  let w2 := Function.update w1 52 (List.replicate (BinaryArithmetic.toNat (w 46)) true)
  have he2' : Eval (Bank.unaryCopyCmd 46 52) t2 (Bank.state r1 w1) (Bank.state r2 w2) := by
    simpa [w1,w2] using he2
  obtain ⟨t3,r3,he3,ht3⟩ := Bank.unaryCopy_eval r2 w2 50 53 (by decide)
    (by simpa [w2,w1] using h53)
  have he3' : Eval (Bank.unaryCopyCmd 50 53) t3
      (Bank.state r2 w2) (Bank.state r3 (unaryWords w)) := by
    simpa [unaryWords,w2,w1] using he3
  have hb1 := unaryCopyBound_le (w 29) (m.val 29) (m.len 29) (hs.1 29) (hs.2 29)
  have hb2 := unaryCopyBound_le (w 46) (m.val 46) (m.len 46) (hs.1 46) (hs.2 46)
  have hb3 := unaryCopyBound_le (w 50) (m.val 50) (m.len 50) (hs.1 50) (hs.2 50)
  simp only [w1,w2,Function.update_of_ne (by decide : (46 : Fin 64)≠51),
    Function.update_of_ne (by decide : (50 : Fin 64)≠51),
    Function.update_of_ne (by decide : (50 : Fin 64)≠52)] at ht2 ht3
  exact ⟨t1+(t2+t3),r3,he1.seq (he2'.seq he3'),by dsimp [unaryRuntime]; omega⟩

theorem finalModel_empty (m : Model) :
    (Interval.finalModel m).len 51=0 ∧
    (Interval.finalModel m).len 52=0 ∧
    (Interval.finalModel m).len 53=0 := by
  simp [Interval.finalModel,Interval.intervalModel,Interval.prepare,
    CacheWidth.code,result,next,output,lengthBound]

/-- These are exactly the three true-unary tapes consumed by the integer
cache bootstrap, plus the preserved binary Qr metadata. -/
theorem output_values (m : Model) (w : Words) (hs : Shape (Interval.finalModel m) w) :
    (unaryWords w) 51=List.replicate (m.val 29) true ∧
    (unaryWords w) 52=List.replicate
      (Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29)) true ∧
    (unaryWords w) 53=List.replicate
      (1+2*Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29)*m.val 29+m.val 21) true ∧
    BinaryArithmetic.toNat ((unaryWords w) 47)=m.val 21*m.val 18 := by
  obtain ⟨hR,hA,hQr,hW⟩ := Interval.final_values m
  simp only [unaryWords,Function.update_self,Function.update_of_ne (by decide : (51 : Fin 64)≠53),
    Function.update_of_ne (by decide : (51 : Fin 64)≠52),
    Function.update_of_ne (by decide : (52 : Fin 64)≠53),
    Function.update_of_ne (by decide : (47 : Fin 64)≠53),
    Function.update_of_ne (by decide : (47 : Fin 64)≠52),
    Function.update_of_ne (by decide : (47 : Fin 64)≠51)]
  exact ⟨congrArg (fun n => List.replicate n true) ((hs.1 29).trans hR),
    congrArg (fun n => List.replicate n true) ((hs.1 46).trans hA),
    congrArg (fun n => List.replicate n true) ((hs.1 50).trans hW),(hs.1 47).trans hQr⟩

abbrev command : Cmd 8 77 := .seq Interval.command unaryCommand
def runtimeBound (m : Model) : ℕ :=
  Interval.runtimeBound m+unaryRuntime (Interval.finalModel m)

/-- Concrete binary and unary cache preparation. The binary intermediate
table is retained in every port except the three declared unary outputs. -/
theorem command_eval (m : Model) (r : Regs) (w : Words) (hs : Shape m w)
    (hr : 0 < m.val 18) :
    ∃ t rf wb, Eval command t (Bank.state r w) (Bank.state rf (unaryWords wb)) ∧
      Shape (Interval.finalModel m) wb ∧ t ≤ runtimeBound m := by
  obtain ⟨t1,r1,wb,he1,hs1,ht1⟩ := Interval.command_eval m r w hs hr
  have hz := finalModel_empty m
  have h51 : wb 51=[] := by have h := hs1.2 51; rw [hz.1] at h; simpa using h
  have h52 : wb 52=[] := by have h := hs1.2 52; rw [hz.2.1] at h; simpa using h
  have h53 : wb 53=[] := by have h := hs1.2 53; rw [hz.2.2] at h; simpa using h
  obtain ⟨t2,r2,he2,ht2⟩ := unary_eval (Interval.finalModel m) r1 wb hs1 h51 h52 h53
  exact ⟨t1+t2,r2,wb,he1.seq he2,hs1,by dsimp [runtimeBound]; omega⟩

def program := compiled command (Bank.port 18) (Bank.port 53)

theorem program_runs (m : Model) (r : Regs) (w : Words) (hs : Shape m w)
    (hr : 0 < m.val 18) :
    ∃ rf wb, RunsIn program (runtimeBound m+1)
      ((Bank.state r w).withPC (some program.entry))
      ((Bank.state rf (unaryWords wb)).withPC none) ∧
      Shape (Interval.finalModel m) wb := by
  obtain ⟨t,rf,wb,he,hshape,ht⟩ := command_eval m r w hs hr
  exact ⟨rf,wb,⟨t+1,Nat.add_le_add_right ht 1,
    compiled_halt_trace he (Bank.port 18) (Bank.port 53)⟩,hshape⟩

theorem program_primitive (m : Model) (r : Regs) (w : Words) (hs : Shape m w)
    (hr : 0 < m.val 18) :
    ∃ rf wb, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(runtimeBound m+1))
      (primitiveCfg program ((Bank.state r w).withPC (some program.entry)))
      (primitiveCfg program ((Bank.state rf (unaryWords wb)).withPC none)) ∧
      Shape (Interval.finalModel m) wb := by
  obtain ⟨rf,wb,he,hshape⟩ := program_runs m r w hs hr
  exact ⟨rf,wb,primitive_execution program he,hshape⟩

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache

end OAI.Algorithms
