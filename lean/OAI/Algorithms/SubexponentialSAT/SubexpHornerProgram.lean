import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl
import OAI.Algorithms.SubexponentialSAT.SubexpTableInterpolation

namespace OAI.Algorithms

/-!
# Fixed-control source generation for factored Horner expressions

Input payloads are coefficient representations, never precomputed instruction
streams. The emitter writes the actual serialized postfix tags and frames.
-/

namespace SubexponentialSAT.SubexpHornerProgram

open BitProgram

def triple {α : Type*} (a b c : α) : Fin 3 → α :=
  fun i => if i = 0 then a else if i = 1 then b else c

@[simp] theorem update_triple_zero {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 0 d = triple d b c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_one {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 1 d = triple a d c := by
  funext i
  fin_cases i <;> simp [triple]

@[simp] theorem update_triple_two {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 2 d = triple a b d := by
  funext i
  fin_cases i <;> simp [triple]

namespace Literal

/-- Ports: payload 0, reverse output 1, empty scratch 2. -/
abbrev program : Program 3 3 13 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 2 true 1
    | 1 => .set 0 false 2
    | 2 => .push 1 0 3
    | 3 => .pop 0 0 1 4
    | 4 => .branch 1 5 8
    | 5 => .push 2 0 6
    | 6 => .push 1 2 7
    | 7 => .push 1 0 3
    | 8 => .push 1 0 9
    | 9 => .pop 2 0 1 10
    | 10 => .branch 1 11 12
    | 11 => .push 0 0 9
    | _ => .halt

def cfg (pc : Option (Fin 13)) (v p c : Bool)
    (payload out scratch : List Bool) : Cfg 3 3 13 :=
  ⟨pc, triple v p c, triple payload out scratch⟩

theorem prefix_trace (payload out : List Bool) (v p c : Bool) :
    Trace program 3 (cfg (some 0) v p c payload out [])
      (cfg (some 3) false p true payload (false :: out) []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, triple]

theorem copy_cycle (b v p : Bool) (bs out scratch : List Bool) :
    Trace program 5 (cfg (some 3) v p true (b :: bs) out scratch)
      (cfg (some 3) b true true bs (b :: true :: out) (b :: scratch)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem copy_finish (v p : Bool) (out scratch : List Bool) :
    Trace program 3 (cfg (some 3) v p true [] out scratch)
      (cfg (some 9) false false true [] (false :: out) scratch) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem copy_trace (payload out scratch : List Bool) (v p : Bool) :
    Trace program (5 * payload.length + 3)
      (cfg (some 3) v p true payload out scratch)
      (cfg (some 9) false false true []
        ((Encoding.frame payload).reverse ++ out) (payload.reverse ++ scratch)) := by
  induction payload generalizing out scratch v p with
  | nil => simpa [Encoding.frame] using copy_finish v p out scratch
  | cons b bs ih =>
      have h := (copy_cycle b v p bs out scratch).trans
        (ih (b :: true :: out) (b :: scratch) b true)
      convert h using 1 <;>
        simp [Encoding.frame, List.reverse_cons, List.append_assoc] ; omega

theorem restore_cycle (b v p : Bool) (bs payload out : List Bool) :
    Trace program 3 (cfg (some 9) v p true payload out (b :: bs))
      (cfg (some 9) b true true (b :: payload) out bs) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem restore_finish (v p : Bool) (payload out : List Bool) :
    Trace program 3 (cfg (some 9) v p true payload out [])
      (cfg none false false true payload out []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem restore_trace (scratch payload out : List Bool) (v p : Bool) :
    Trace program (3 * scratch.length + 3)
      (cfg (some 9) v p true payload out scratch)
      (cfg none false false true (scratch.reverse ++ payload) out []) := by
  induction scratch generalizing payload v p with
  | nil => simpa using restore_finish v p payload out
  | cons b bs ih =>
      have h := (restore_cycle b v p bs payload out).trans (ih (b :: payload) b true)
      convert h using 1 <;> simp [List.reverse_cons, List.append_assoc] ; omega

/-- Copy a raw literal payload, frame it, and emit its push opcode. The
payload is restored exactly and the scratch port is again empty. -/
theorem trace (payload out : List Bool) (v p c : Bool) :
    Trace program (8 * payload.length + 9)
      (cfg (some 0) v p c payload out [])
      (cfg none false false true payload
        ((false :: Encoding.frame payload).reverse ++ out) []) := by
  have hc := copy_trace payload (false :: out) [] false p
  simp only [List.append_nil] at hc
  have hr := restore_trace payload.reverse []
    ((Encoding.frame payload).reverse ++ false :: out) false false
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  have h := (prefix_trace payload out v p c).trans (hc.trans hr)
  convert h using 1 <;> (try simp [List.reverse_cons, List.append_assoc]) ; omega

theorem primitive_execution (payload out : List Bool) (v p c : Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (8 * payload.length + 9))
      (BitProgram.primitiveCfg program (cfg (some 0) v p c payload out []))
      (BitProgram.primitiveCfg program (cfg none false false true payload
        ((false :: Encoding.frame payload).reverse ++ out) [])) :=
  BitProgram.primitive_execution program ⟨_, le_rfl, trace payload out v p c⟩

end Literal

end SubexponentialSAT.SubexpHornerProgram

end OAI.Algorithms
