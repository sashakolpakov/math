import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgram
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.ProgramLinking
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Fixed-control skipping of framed CNF records

The program below has three Boolean registers, one Boolean stack, and eleven
fixed labels. It consumes an escaped frame or one tagged list item without
materializing the payload. The payload may itself encode a list of literals,
a clause, or a more deeply nested record. Every bound is proved for actual
`BitProgram.step` traces, rather than assigned to a semantic list operation.
-/

namespace SubexponentialSAT.ExecCNFRecords

open SubexponentialSAT.BitProgram

/-- Registers 0, 1, 2 hold the last bit, presence flag, and item-found flag. -/
def regs (value present found : Bool) : Fin 3 → Bool :=
  fun i => if i = 0 then value else if i = 1 then present else found

@[simp] theorem regs_zero (v p f : Bool) : regs v p f 0 = v := rfl
@[simp] theorem regs_one (v p f : Bool) : regs v p f 1 = p := rfl
@[simp] theorem regs_two (v p f : Bool) : regs v p f 2 = f := rfl

@[simp] theorem update_regs_zero (v p f b : Bool) :
    Function.update (regs v p f) 0 b = regs b p f := by
  funext i
  fin_cases i <;> simp [regs]

@[simp] theorem update_regs_one (v p f b : Bool) :
    Function.update (regs v p f) 1 b = regs v b f := by
  funext i
  fin_cases i <;> simp [regs]

@[simp] theorem update_regs_two (v p f b : Bool) :
    Function.update (regs v p f) 2 b = regs v p b := by
  funext i
  fin_cases i <;> simp [regs]

@[simp] theorem update_stack (input output : List Bool) :
    Function.update (fun _ : Fin 1 => input) 0 output = fun _ : Fin 1 => output := by
  funext i
  fin_cases i
  simp

/-- Entry 0 reads a tagged list item; entry 4 reads a raw escape frame. -/
abbrev skipProgram : Program 3 1 11 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 10
    | 2 => .branch 0 3 9
    | 3 => .set 2 true 4
    | 4 => .pop 0 0 1 5
    | 5 => .branch 1 6 10
    | 6 => .branch 0 7 10
    | 7 => .pop 0 0 1 8
    | 8 => .branch 1 4 10
    | 9 => .set 2 false 10
    | _ => .halt

def cfg (pc : Option (Fin 11)) (value present found : Bool) (input : List Bool) :
    Cfg 3 1 11 := ⟨pc, regs value present found, fun _ => input⟩

theorem start_pop (b v p f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 0) v p f (b :: input)) =
      some (cfg (some 1) b true f input) := by
  simp [step, cfg, execInstr, readRegs]

theorem start_present (v f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 1) v true f input) =
      some (cfg (some 2) v true f input) := by
  simp [step, cfg, execInstr]

theorem start_true (f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 2) true true f input) =
      some (cfg (some 3) true true f input) := by
  simp [step, cfg, execInstr]

theorem mark_found (f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 3) true true f input) =
      some (cfg (some 4) true true true input) := by
  simp [step, cfg, execInstr]

theorem frame_pop_tag (b v p f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 4) v p f (b :: input)) =
      some (cfg (some 5) b true f input) := by
  simp [step, cfg, execInstr, readRegs]

theorem frame_present_tag (v f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 5) v true f input) =
      some (cfg (some 6) v true f input) := by
  simp [step, cfg, execInstr]

theorem frame_true_tag (f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 6) true true f input) =
      some (cfg (some 7) true true f input) := by
  simp [step, cfg, execInstr]

theorem frame_pop_data (b v p f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 7) v p f (b :: input)) =
      some (cfg (some 8) b true f input) := by
  simp [step, cfg, execInstr, readRegs]

theorem frame_present_data (v f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 8) v true f input) =
      some (cfg (some 4) v true f input) := by
  simp [step, cfg, execInstr]

theorem frame_false_tag (f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 6) false true f input) =
      some (cfg (some 10) false true f input) := by
  simp [step, cfg, execInstr]

theorem skip_halt (v p f : Bool) (input : List Bool) :
    step skipProgram (cfg (some 10) v p f input) =
      some (cfg none v p f input) := by
  simp [step, cfg, execInstr]

theorem record_prefix (v p f : Bool) (input : List Bool) :
    Trace skipProgram 4 (cfg (some 0) v p f (true :: input))
      (cfg (some 4) true true true input) :=
  .cons (start_pop true v p f input)
    (.cons (start_present true f input)
      (.cons (start_true f input) (.cons (mark_found f input) (.refl _))))

theorem frame_cycle (b v p f : Bool) (input : List Bool) :
    Trace skipProgram 5 (cfg (some 4) v p f (true :: b :: input))
      (cfg (some 4) b true f input) :=
  .cons (frame_pop_tag true v p f (b :: input))
    (.cons (frame_present_tag true f (b :: input))
      (.cons (frame_true_tag f (b :: input))
        (.cons (frame_pop_data b true true f input)
          (.cons (frame_present_data b f input) (.refl _)))))

theorem frame_finish (v p f : Bool) (input : List Bool) :
    Trace skipProgram 4 (cfg (some 4) v p f (false :: input))
      (cfg none false true f input) :=
  .cons (frame_pop_tag false v p f input)
    (.cons (frame_present_tag false f input)
      (.cons (frame_false_tag f input) (.cons (skip_halt false true f input) (.refl _))))

/-- Raw-frame entry consumes exactly one frame and preserves the entire suffix. -/
theorem frame_trace (bits rest : List Bool) (v p f : Bool) :
    Trace skipProgram (5 * bits.length + 4)
      (cfg (some 4) v p f (Encoding.frame bits ++ rest))
      (cfg none false true f rest) := by
  induction bits generalizing v p with
  | nil => simpa [Encoding.frame_nil] using frame_finish v p f rest
  | cons b bits ih =>
      have h := (frame_cycle b v p f (Encoding.frame bits ++ rest)).trans (ih b true)
      have ht : 5 + (5 * bits.length + 4) = 5 * (b :: bits).length + 4 := by
        simp only [List.length_cons]
        omega
      simpa only [ht, Encoding.frame_cons, List.cons_append] using h

/-- Public entry skips one tagged record, reporting that an item was present. -/
theorem record_trace (bits rest : List Bool) (v p f : Bool) :
    Trace skipProgram (5 * bits.length + 8)
      (cfg (some 0) v p f (true :: (Encoding.frame bits ++ rest)))
      (cfg none false true true rest) := by
  have h := (record_prefix v p f (Encoding.frame bits ++ rest)).trans
    (frame_trace bits rest true true true)
  have ht : 4 + (5 * bits.length + 4) = 5 * bits.length + 8 := by omega
  simpa only [ht] using h

/-- End-of-list is distinct from a successfully skipped record. -/
theorem list_end_trace (rest : List Bool) (v p f : Bool) :
    Trace skipProgram 5 (cfg (some 0) v p f (false :: rest))
      (cfg none false true false rest) := by
  have hfalse : step skipProgram (cfg (some 2) false true f rest) =
      some (cfg (some 9) false true f rest) := by
    simp [step, cfg, execInstr]
  have hmark : step skipProgram (cfg (some 9) false true f rest) =
      some (cfg (some 10) false true false rest) := by
    simp [step, cfg, execInstr]
  exact .cons (start_pop false v p f rest)
    (.cons (start_present false f rest)
      (.cons hfalse (.cons hmark (.cons (skip_halt false true false rest) (.refl _)))))

/-- Missing input is rejected by the presence flag, rather than read as a delimiter. -/
theorem empty_reject (v p f : Bool) :
    Trace skipProgram 3 (cfg (some 0) v p f []) (cfg none false false f []) := by
  have hpop : step skipProgram (cfg (some 0) v p f []) =
      some (cfg (some 1) false false f []) := by
    simp [step, cfg, execInstr, readRegs]
  have hbranch : step skipProgram (cfg (some 1) false false f []) =
      some (cfg (some 10) false false f []) := by
    simp [step, cfg, execInstr]
  exact .cons hpop (.cons hbranch (.cons (skip_halt false false f []) (.refl _)))

/-- Linear actual-step bound in the encoded input length; no payload-size oracle. -/
theorem record_runsIn_length (bits rest : List Bool) (v p f : Bool) :
    RunsIn skipProgram (4 * (true :: (Encoding.frame bits ++ rest)).length)
      (cfg (some 0) v p f (true :: (Encoding.frame bits ++ rest)))
      (cfg none false true true rest) := by
  refine ⟨5 * bits.length + 8, ?_, record_trace bits rest v p f⟩
  simp only [List.length_cons, List.length_append, Encoding.length_frame]
  omega

/-- Frame-entry cost is likewise linear in the actual encoded bytes/bits. -/
theorem frame_runsIn_length (bits rest : List Bool) (v p f : Bool) :
    RunsIn skipProgram (4 * (Encoding.frame bits ++ rest).length)
      (cfg (some 4) v p f (Encoding.frame bits ++ rest))
      (cfg none false true f rest) := by
  refine ⟨5 * bits.length + 4, ?_, frame_trace bits rest v p f⟩
  simp only [List.length_append, Encoding.length_frame]
  omega

/-- Each list item can contain an arbitrarily nested encoding. -/
theorem list_cons_trace {α : Type*} (enc : α → List Bool) (a : α) (as : List α)
    (suffix : List Bool) (v p f : Bool) :
    Trace skipProgram (5 * (enc a).length + 8)
      (cfg (some 0) v p f (Encoding.encodeList enc (a :: as) ++ suffix))
      (cfg none false true true (Encoding.encodeList enc as ++ suffix)) := by
  simpa only [Encoding.encodeList, List.cons_append, List.append_assoc] using
    record_trace (enc a) (Encoding.encodeList enc as ++ suffix) v p f

/-- In particular, skip a whole clause whose payload is a framed list of naturals. -/
theorem clause_record_trace (C : List ℕ) (F : List (List ℕ)) (suffix : List Bool)
    (v p f : Bool) :
    Trace skipProgram (5 * (Encoding.encodeList Encoding.encodeNat C).length + 8)
      (cfg (some 0) v p f
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (C :: F) ++ suffix))
      (cfg none false true true
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F ++ suffix)) :=
  list_cons_trace (Encoding.encodeList Encoding.encodeNat) C F suffix v p f

/-- The decoded clause suffix agrees with the actual record traversal. -/
theorem frame_read_agrees (bits rest : List Bool) :
    Encoding.readFrame (Encoding.frame bits ++ rest) = some (bits, rest) :=
  Encoding.readFrame_frame_append bits rest

end SubexponentialSAT.ExecCNFRecords

namespace SubexponentialSAT.ExecCNFRecords
open SubexponentialSAT.BitProgram

/-- Source, destination and scratch are fixed ports 0, 1 and 2. -/
def ports {α : Type*} (source destination scratch : α) : Fin 3 → α :=
  fun i => if i = 0 then source else if i = 1 then destination else scratch

@[simp] theorem ports_zero {α : Type*} (a b c : α) : ports a b c 0 = a := rfl
@[simp] theorem ports_one {α : Type*} (a b c : α) : ports a b c 1 = b := rfl
@[simp] theorem ports_two {α : Type*} (a b c : α) : ports a b c 2 = c := rfl

@[simp] theorem update_ports_zero {α : Type*} (a b c d : α) :
    Function.update (ports a b c) 0 d = ports d b c := by
  funext i
  fin_cases i <;> simp [ports]
@[simp] theorem update_ports_one {α : Type*} (a b c d : α) :
    Function.update (ports a b c) 1 d = ports a d c := by
  funext i
  fin_cases i <;> simp [ports]
@[simp] theorem update_ports_two {α : Type*} (a b c d : α) :
    Function.update (ports a b c) 2 d = ports a b d := by
  funext i
  fin_cases i <;> simp [ports]

def copyCfg {l : ℕ} (pc : Option (Fin l)) (v p : Bool)
    (source destination scratch : List Bool) : Cfg 2 3 l :=
  ⟨pc, ParserProgram.pair v p, ports source destination scratch⟩

/-- Capture the raw bits of one frame or tagged record in reverse on scratch.
Destination port 1 is untouched. -/
abbrev captureProgram : Program 2 3 12 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 11
    | 2 => .branch 0 3 11
    | 3 => .push 2 0 4
    | 4 => .pop 0 0 1 5
    | 5 => .branch 1 6 11
    | 6 => .push 2 0 7
    | 7 => .branch 0 8 11
    | 8 => .pop 0 0 1 9
    | 9 => .branch 1 10 11
    | 10 => .push 2 0 4
    | _ => .halt

theorem capture_pop_start (b v p : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 0) v p (b :: input) output scratch) =
      some (copyCfg (some 1) b true input output scratch) := by
  simp [step, copyCfg, execInstr, readRegs]

theorem capture_present_start (v : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 1) v true input output scratch) =
      some (copyCfg (some 2) v true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_true_start (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 2) true true input output scratch) =
      some (copyCfg (some 3) true true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_push_start (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 3) true true input output scratch) =
      some (copyCfg (some 4) true true input output (true :: scratch)) := by
  simp [step, copyCfg, execInstr]

theorem capture_pop_tag (b v p : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 4) v p (b :: input) output scratch) =
      some (copyCfg (some 5) b true input output scratch) := by
  simp [step, copyCfg, execInstr, readRegs]

theorem capture_present_tag (v : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 5) v true input output scratch) =
      some (copyCfg (some 6) v true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_push_tag (v : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 6) v true input output scratch) =
      some (copyCfg (some 7) v true input output (v :: scratch)) := by
  simp [step, copyCfg, execInstr]

theorem capture_true_tag (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 7) true true input output scratch) =
      some (copyCfg (some 8) true true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_pop_data (b v p : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 8) v p (b :: input) output scratch) =
      some (copyCfg (some 9) b true input output scratch) := by
  simp [step, copyCfg, execInstr, readRegs]

theorem capture_present_data (v : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 9) v true input output scratch) =
      some (copyCfg (some 10) v true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_push_data (b : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 10) b true input output scratch) =
      some (copyCfg (some 4) b true input output (b :: scratch)) := by
  simp [step, copyCfg, execInstr]

theorem capture_false_tag (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 7) false true input output scratch) =
      some (copyCfg (some 11) false true input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_halt (v p : Bool) (input output scratch : List Bool) :
    step captureProgram (copyCfg (some 11) v p input output scratch) =
      some (copyCfg none v p input output scratch) := by
  simp [step, copyCfg, execInstr]

theorem capture_prefix (v p : Bool) (input output scratch : List Bool) :
    Trace captureProgram 4 (copyCfg (some 0) v p (true :: input) output scratch)
      (copyCfg (some 4) true true input output (true :: scratch)) :=
  .cons (capture_pop_start true v p input output scratch)
    (.cons (capture_present_start true input output scratch)
      (.cons (capture_true_start input output scratch)
        (.cons (capture_push_start input output scratch) (.refl _))))

theorem capture_cycle (b v p : Bool) (input output scratch : List Bool) :
    Trace captureProgram 7 (copyCfg (some 4) v p (true :: b :: input) output scratch)
      (copyCfg (some 4) b true input output (b :: true :: scratch)) :=
  .cons (capture_pop_tag true v p (b :: input) output scratch)
    (.cons (capture_present_tag true (b :: input) output scratch)
      (.cons (capture_push_tag true (b :: input) output scratch)
        (.cons (capture_true_tag (b :: input) output (true :: scratch))
          (.cons (capture_pop_data b true true input output (true :: scratch))
            (.cons (capture_present_data b input output (true :: scratch))
              (.cons (capture_push_data b input output (true :: scratch)) (.refl _)))))))

theorem capture_finish (v p : Bool) (input output scratch : List Bool) :
    Trace captureProgram 5 (copyCfg (some 4) v p (false :: input) output scratch)
      (copyCfg none false true input output (false :: scratch)) :=
  .cons (capture_pop_tag false v p input output scratch)
    (.cons (capture_present_tag false input output scratch)
      (.cons (capture_push_tag false input output scratch)
        (.cons (capture_false_tag input output (false :: scratch))
          (.cons (capture_halt false true input output (false :: scratch)) (.refl _)))))

theorem capture_frame_trace (bits rest output scratch : List Bool) (v p : Bool) :
    Trace captureProgram (7 * bits.length + 5)
      (copyCfg (some 4) v p (Encoding.frame bits ++ rest) output scratch)
      (copyCfg none false true rest output ((Encoding.frame bits).reverse ++ scratch)) := by
  induction bits generalizing v p scratch with
  | nil => simpa [Encoding.frame_nil] using capture_finish v p rest output scratch
  | cons b bits ih =>
      have h := (capture_cycle b v p (Encoding.frame bits ++ rest) output scratch).trans
        (ih (b :: true :: scratch) b true)
      have ht : 7 + (7 * bits.length + 5) = 7 * (b :: bits).length + 5 := by
        simp only [List.length_cons]
        omega
      simpa only [ht, Encoding.frame_cons, List.cons_append, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append] using h

theorem capture_record_trace (bits rest output scratch : List Bool) (v p : Bool) :
    Trace captureProgram (7 * bits.length + 9)
      (copyCfg (some 0) v p (true :: (Encoding.frame bits ++ rest)) output scratch)
      (copyCfg none false true rest output ((true :: Encoding.frame bits).reverse ++ scratch)) := by
  have h := (capture_prefix v p (Encoding.frame bits ++ rest) output scratch).trans
    (capture_frame_trace bits rest output (true :: scratch) true true)
  have ht : 4 + (7 * bits.length + 5) = 7 * bits.length + 9 := by omega
  simpa only [ht, List.reverse_cons, List.append_assoc, List.singleton_append] using h

/-- Restore the captured word to forward order on the destination port. -/
abbrev restoreCapturedProgram : Program 2 3 4 := StackRoutines.transferProgram 2 1 0 1

theorem restoreCaptured_trace (input output scratch : List Bool) (v p : Bool) :
    Trace restoreCapturedProgram (3 * scratch.length + 3)
      (copyCfg (some 0) v p input output scratch)
      (copyCfg none false false input (scratch.reverse ++ output) []) := by
  have h := StackRoutines.transferProgram_trace (r := 2) (s := 3)
    2 1 0 1 (by decide) (by decide) (ParserProgram.pair v p) (ports input output scratch)
  have ht : Trace restoreCapturedProgram (3 * scratch.length + 2)
      (copyCfg (some 0) v p input output scratch)
      (copyCfg (some 3) false false input (scratch.reverse ++ output) []) := by
    simpa [restoreCapturedProgram, copyCfg, StackRoutines.transferResult,
      StackRoutines.transferStacks, readRegs] using h
  have hh : step restoreCapturedProgram
      (copyCfg (some 3) false false input (scratch.reverse ++ output) []) =
      some (copyCfg none false false input (scratch.reverse ++ output) []) := by
    simp [step, copyCfg, execInstr]
  simpa [Nat.add_assoc] using ht.trans (.cons hh (.refl _))

/-- Sixteen fixed labels copy a whole raw record while consuming only that
record at the source. Its source suffix and old destination are preserved. -/
abbrev copyProgram : Program 2 3 16 := ProgramLinking.link captureProgram restoreCapturedProgram

/-- Copy a tagged record in original encoded order; scratch is restored empty. -/
theorem copy_record_trace (bits rest output : List Bool) (v p : Bool) :
    Trace copyProgram (13 * bits.length + 18)
      (copyCfg (some 0) v p (true :: (Encoding.frame bits ++ rest)) output [])
      (copyCfg none false false rest ((true :: Encoding.frame bits) ++ output) []) := by
  have hp : Trace captureProgram (7 * bits.length + 9)
      (copyCfg (some 0) v p (true :: (Encoding.frame bits ++ rest)) output [])
      (copyCfg none false true rest output (true :: Encoding.frame bits).reverse) := by
    simpa using capture_record_trace bits rest output [] v p
  have hq : Trace restoreCapturedProgram (3 * (true :: Encoding.frame bits).length + 3)
      (ProgramLinking.enter restoreCapturedProgram
        (copyCfg (l := 12) none false true rest output (true :: Encoding.frame bits).reverse))
      (copyCfg none false false rest ((true :: Encoding.frame bits) ++ output) []) := by
    simpa [ProgramLinking.enter, restoreCapturedProgram, StackRoutines.transferProgram, copyCfg]
      using restoreCaptured_trace rest output (true :: Encoding.frame bits).reverse false true
  have h := ProgramLinking.link_trace captureProgram restoreCapturedProgram hp rfl hq
  have hc : (7 * bits.length + 9) + (3 * (true :: Encoding.frame bits).length + 3) =
      13 * bits.length + 18 := by
    simp only [List.length_cons, Encoding.length_frame]
    omega
  have hzero : Fin.castAdd 4 (0 : Fin 12) = (0 : Fin 16) := rfl
  simpa only [hc, copyProgram, ProgramLinking.relabelCfg, ProgramLinking.relocatePc,
    copyCfg, hzero]
    using h

/-- Raw-frame entry 4 copies a frame, including its escapes and delimiter. -/
theorem copy_frame_trace (bits rest output : List Bool) (v p : Bool) :
    Trace copyProgram (13 * bits.length + 11)
      (copyCfg (some 4) v p (Encoding.frame bits ++ rest) output [])
      (copyCfg none false false rest (Encoding.frame bits ++ output) []) := by
  have hp : Trace captureProgram (7 * bits.length + 5)
      (copyCfg (some 4) v p (Encoding.frame bits ++ rest) output [])
      (copyCfg none false true rest output (Encoding.frame bits).reverse) := by
    simpa using capture_frame_trace bits rest output [] v p
  have hq : Trace restoreCapturedProgram (3 * (Encoding.frame bits).length + 3)
      (ProgramLinking.enter restoreCapturedProgram
        (copyCfg (l := 12) none false true rest output (Encoding.frame bits).reverse))
      (copyCfg none false false rest (Encoding.frame bits ++ output) []) := by
    simpa [ProgramLinking.enter, restoreCapturedProgram, StackRoutines.transferProgram, copyCfg]
      using restoreCaptured_trace rest output (Encoding.frame bits).reverse false true
  have h := ProgramLinking.link_trace captureProgram restoreCapturedProgram hp rfl hq
  have hc : (7 * bits.length + 5) + (3 * (Encoding.frame bits).length + 3) =
      13 * bits.length + 11 := by
    simp only [Encoding.length_frame]
    omega
  have hfour : Fin.castAdd 4 (4 : Fin 12) = (4 : Fin 16) := rfl
  simpa only [hc, copyProgram, ProgramLinking.relabelCfg, ProgramLinking.relocatePc,
    copyCfg, hfour]
    using h

theorem copy_record_runsIn_length (bits rest output : List Bool) (v p : Bool) :
    RunsIn copyProgram (9 * (true :: (Encoding.frame bits ++ rest)).length)
      (copyCfg (some 0) v p (true :: (Encoding.frame bits ++ rest)) output [])
      (copyCfg none false false rest ((true :: Encoding.frame bits) ++ output) []) := by
  refine ⟨13 * bits.length + 18, ?_, copy_record_trace bits rest output v p⟩
  simp only [List.length_cons, List.length_append, Encoding.length_frame]
  omega

theorem copy_frame_runsIn_length (bits rest output : List Bool) (v p : Bool) :
    RunsIn copyProgram (11 * (Encoding.frame bits ++ rest).length)
      (copyCfg (some 4) v p (Encoding.frame bits ++ rest) output [])
      (copyCfg none false false rest (Encoding.frame bits ++ output) []) := by
  refine ⟨13 * bits.length + 11, ?_, copy_frame_trace bits rest output v p⟩
  simp only [List.length_append, Encoding.length_frame]
  omega

theorem copy_clause_record_trace (C : List ℕ) (F : List (List ℕ))
    (suffix output : List Bool) (v p : Bool) :
    Trace copyProgram (13 * (Encoding.encodeList Encoding.encodeNat C).length + 18)
      (copyCfg (some 0) v p
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (C :: F) ++ suffix) output [])
      (copyCfg none false false
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F ++ suffix)
        ((true :: Encoding.frame (Encoding.encodeList Encoding.encodeNat C)) ++ output) []) := by
  simpa only [Encoding.encodeList, List.cons_append, List.append_assoc] using
    copy_record_trace (Encoding.encodeList Encoding.encodeNat C)
      (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F ++ suffix) output v p

end SubexponentialSAT.ExecCNFRecords

end OAI.Algorithms
