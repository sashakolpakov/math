import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheControl
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCofactorLoop

namespace OAI.Algorithms

/-! Exact byte-level composition for the source-field cache scans. -/

namespace SubexponentialSAT.SubexpFieldCacheLoop

open BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open SubexpCRTCofactorControl SubexpFieldCacheControl

theorem copy_node_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (hn : w.negative = []) :
    Eval (SubexpFieldCacheControl.copy 94 95) (7 * w.node.length + 5)
      (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with negative := w.node}) := by
  have h := copy_eval (state regs frame w) 94 95 0 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have he : afterCopy (state regs frame w) 94 95 0 1 =
      state (readRegs regs 0 1 none) frame {w with negative := w.node} := by
    simp only [afterCopy, state, copyStacks, store_node, store_negative, hn,
      List.append_nil, update_store_negative]
  rw [he] at h
  simpa only [SubexpFieldCacheControl.copy, state, store_node] using h

theorem clear_negative_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) :
    Eval (clear 95) (2 * w.negative.length + 3) (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with negative := []}) := by
  have h := SubexpCRTCofactorLoop.clear_eval (state regs frame w) 95
  simpa only [state, store_negative, update_store_negative] using h

theorem clear_node_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) :
    Eval (clear 94) (2 * w.node.length + 3) (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with node := []}) := by
  have h := SubexpCRTCofactorLoop.clear_eval (state regs frame w) 94
  simpa only [state, store_node, update_store_node] using h

theorem emit_inverse_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) :
    Eval (emit 96 98) (3 * w.power.length + 3) (state regs frame w)
      (state (readRegs regs 0 1 none) frame
        {w with power := [], accumulator := w.power.reverse ++ w.accumulator}) := by
  have h := transfer_eval (state regs frame w) 96 98 0 1 (by decide) (by decide)
  have he : afterTransfer (state regs frame w) 96 98 0 1 =
      state (readRegs regs 0 1 none) frame
        {w with power := [], accumulator := w.power.reverse ++ w.accumulator} := by
    simp only [afterTransfer, state, transferStacks, store_power, store_accumulator,
      update_store_power, update_store_accumulator]
  rw [he] at h
  simpa only [emit, state, store_power] using h

theorem emit_negative_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) :
    Eval (emit 95 100) (3 * w.negative.length + 3) (state regs frame w)
      (state (readRegs regs 0 1 none)
        (Function.update frame 100 (w.negative.reverse ++ frame 100))
        {w with negative := []}) := by
  have h := transfer_eval (state regs frame w) 95 100 0 1 (by decide) (by decide)
  have he : afterTransfer (state regs frame w) 95 100 0 1 =
      state (readRegs regs 0 1 none)
        (Function.update frame 100 (w.negative.reverse ++ frame 100))
        {w with negative := []} := by
    simp only [afterTransfer, state, transferStacks, store_negative,
      store_extra frame w 100 (by right; left; rfl), update_store_negative,
      update_store_extra _ _ 100 _ (by right; left; rfl)]
  rw [he] at h
  simpa only [emit, state, store_negative] using h

def taken (w : Words) (bits rest : List Bool) : Words :=
  {w with stream := rest, node := bits}

def nodePowerInput (w : Words) (bits rest : List Bool) : Words :=
  {taken w bits rest with negative := bits}

def nodeNegationInput (w : Words) (bits rest inverse : List Bool) : Words :=
  {taken w bits rest with negative := [], power := inverse}

def nodeOutput (w : Words) (rest inverse : List Bool) : Words :=
  {w with
    stream := rest, node := [], negative := [], power := []
    accumulator := inverse.reverse ++ w.accumulator}

/-- The arithmetic premises are concrete executions of the supplied fixed
tables; all parsing, copying, emission, and cleanup is proved here. -/
theorem nodeIteration_eval (negate power : Cmd 8 110)
    (regs rp rn : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words)
    (bits rest inverse negative : List Bool) (np nn : ℕ)
    (hs : w.stream = bits ++ rest) (hw : w.blockWidth.length = bits.length)
    (hn : w.node = []) (hneg : w.negative = [])
    (hpower : Eval power np
      (state (readRegs regs 0 1 none) frame (nodePowerInput w bits rest))
      (state rp frame {nodePowerInput w bits rest with power := inverse}))
    (hnegative : Eval negate nn
      (state (readRegs rp 0 1 none) frame (nodeNegationInput w bits rest inverse))
      (state rn frame {nodeNegationInput w bits rest inverse with negative := negative})) :
    Eval (nodeIteration negate power)
      (25 * bits.length + 3 * inverse.length + 3 * negative.length + np + nn + 28)
      (state regs frame w)
      (state (readRegs rn 0 1 none)
        (Function.update frame 100 (negative.reverse ++ frame 100))
        (nodeOutput w rest inverse)) := by
  have h1 := takeNode_eval regs frame w bits rest hs hw hn
  have h2 := copy_node_eval (readRegs regs 0 1 none) frame (taken w bits rest)
    (by simpa only [taken] using hneg)
  have h3 := clear_negative_eval rp frame {nodePowerInput w bits rest with power := inverse}
  have h4 := emit_inverse_eval rn frame
    {nodeNegationInput w bits rest inverse with negative := negative}
  let w4 : Words := {nodeNegationInput w bits rest inverse with
    negative := negative, power := [], accumulator := inverse.reverse ++ w.accumulator}
  have h5 := emit_negative_eval (readRegs rn 0 1 none) frame w4
  have h6 := clear_node_eval (readRegs rn 0 1 none)
    (Function.update frame 100 (negative.reverse ++ frame 100)) {w4 with negative := []}
  simp only [readRegs_reset] at h2 h5 h6
  have ht := h1.seq (h2.seq (hpower.seq (h3.seq (hnegative.seq (h4.seq (h5.seq h6))))))
  convert ht using 1
  · simp only [nodePowerInput, nodeNegationInput, taken, w4]
    omega
  · rfl

theorem emit_difference_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) :
    Eval (emit 96 103) (3 * w.power.length + 3) (state regs frame w)
      (state (readRegs regs 0 1 none)
        (Function.update frame 103 (w.power.reverse ++ frame 103))
        {w with power := []}) := by
  have h := transfer_eval (state regs frame w) 96 103 0 1 (by decide) (by decide)
  have he : afterTransfer (state regs frame w) 96 103 0 1 =
      state (readRegs regs 0 1 none)
        (Function.update frame 103 (w.power.reverse ++ frame 103))
        {w with power := []} := by
    simp only [afterTransfer, state, transferStacks, store_power,
      store_extra frame w 103 (by right; right; left; rfl), update_store_power,
      update_store_extra _ _ 103 _ (by right; right; left; rfl)]
  rw [he] at h
  simpa only [emit, state, store_power] using h

theorem take_negative_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (bits rest : List Bool) (hs : w.stream = bits ++ rest)
    (hw : w.blockWidth.length = bits.length) (hn : w.negative = []) :
    Eval (takeWord 104 107 108 99 95 0 1) (14 * bits.length + 11)
      (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with stream := rest, negative := bits}) := by
  have h := takeWord_eval (state regs frame w) 104 107 108 99 95 0 1
    (by decide) (by decide) bits rest
    (by simpa [state] using hs) (by simp [state]) (by simp [state])
    (by simpa [state] using hw)
  have he : afterTake (state regs frame w) 99 95 0 1 bits rest =
      state (readRegs regs 0 1 none) frame {w with stream := rest, negative := bits} := by
    simp only [afterTake, state, store_negative, hn, List.append_nil,
      update_store_stream, update_store_negative]
  simpa only [he] using h

theorem copy_left_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (hl : w.left = []) :
    Eval (SubexpFieldCacheControl.copy 94 70) (7 * w.node.length + 5)
      (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with left := w.node}) := by
  have h := copy_eval (state regs frame w) 94 70 0 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have he : afterCopy (state regs frame w) 94 70 0 1 =
      state (readRegs regs 0 1 none) frame {w with left := w.node} := by
    simp only [afterCopy, state, copyStacks, store_node, store_left, hl,
      List.append_nil, update_store_left]
  rw [he] at h
  simpa only [SubexpFieldCacheControl.copy, state, store_node] using h

theorem move_sum_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (hn : w.negative = []) :
    Eval (move 70 95) (6 * w.left.length + 6) (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with left := [], negative := w.left}) := by
  have h := move_eval (state regs frame w) 70 95
    (by decide) (by decide) (by decide) (by simp [state])
    (by simpa [state] using hn)
  simpa only [moved, state, store_left, update_store_left, update_store_negative] using h

def pairAddInput (w : Words) (bits rest : List Bool) : Words :=
  {w with stream := rest, negative := bits, left := w.node}

def pairPowerInput (w : Words) (rest sum : List Bool) : Words :=
  {w with stream := rest, left := [], negative := sum}

def pairOutput (w : Words) (rest : List Bool) : Words :=
  {w with stream := rest, left := [], negative := [], power := []}

/-- One inner-row iteration emits exactly one output block. The current
positive node survives, so the next inner iteration uses the same row. -/
theorem pairIteration_eval (add power : Cmd 8 110)
    (regs ra rp : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words)
    (bits rest sum inverse : List Bool) (na np : ℕ)
    (hs : w.stream = bits ++ rest) (hw : w.blockWidth.length = bits.length)
    (hn : w.negative = []) (hl : w.left = [])
    (hadd : Eval add na
      (state (readRegs regs 0 1 none) frame (pairAddInput w bits rest))
      (state ra frame {pairAddInput w bits rest with left := sum, negative := []}))
    (hpower : Eval power np
      (state (readRegs ra 0 1 none) frame (pairPowerInput w rest sum))
      (state rp frame {pairPowerInput w rest sum with power := inverse})) :
    Eval (pairIteration add power)
      (14 * bits.length + 7 * w.node.length + 8 * sum.length + 3 * inverse.length + na + np + 28)
      (state regs frame w)
      (state (readRegs rp 0 1 none)
        (Function.update frame 103 (inverse.reverse ++ frame 103)) (pairOutput w rest)) := by
  have h1 := take_negative_eval regs frame w bits rest hs hw hn
  have h2 := copy_left_eval (readRegs regs 0 1 none) frame
    {w with stream := rest, negative := bits} hl
  have h3 := move_sum_eval ra frame {pairAddInput w bits rest with left := sum, negative := []} rfl
  have h4 := clear_negative_eval rp frame {pairPowerInput w rest sum with power := inverse}
  have h5 := emit_difference_eval (readRegs rp 0 1 none) frame
    {pairPowerInput w rest sum with power := inverse, negative := []}
  simp only [readRegs_reset] at h2 h5
  have ht := h1.seq (h2.seq (hadd.seq (h3.seq (hpower.seq (h4.seq h5)))))
  convert ht using 1
  · simp only [pairPowerInput]
    omega
  · rfl

theorem copy_extra_stream_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (src : Fin 110) (hsrc : extra src) (hs : w.stream = []) :
    Eval (SubexpFieldCacheControl.copy src 99) (7 * (frame src).length + 5)
      (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with stream := frame src}) := by
  have h99 : src ≠ 99 := by rcases hsrc with rfl | rfl | rfl | rfl <;> decide
  have h0 : src ≠ 0 := by rcases hsrc with rfl | rfl | rfl | rfl <;> decide
  have h := copy_eval (state regs frame w) src 99 0 0 1
    h99 h0 (by decide) (by decide) (by simp [state])
  have he : afterCopy (state regs frame w) src 99 0 1 =
      state (readRegs regs 0 1 none) frame {w with stream := frame src} := by
    simp only [afterCopy, state, copyStacks, store_extra frame w src hsrc,
      store_stream, hs, List.append_nil, update_store_stream]
  rw [he] at h
  simpa only [SubexpFieldCacheControl.copy, state, store_extra frame w src hsrc] using h

theorem take_outer_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (bits rest : List Bool) (hs : frame 106 = bits ++ rest)
    (hw : w.blockWidth.length = bits.length) (hn : w.node = []) :
    Eval (takeWord 104 107 108 106 94 0 1) (14 * bits.length + 11)
      (state regs frame w)
      (state (readRegs regs 0 1 none) (Function.update frame 106 rest) {w with node := bits}) := by
  have h := takeWord_eval (state regs frame w) 104 107 108 106 94 0 1
    (by decide) (by decide) bits rest
    (by simpa [state, store] using hs) (by simp [state]) (by simp [state])
    (by simpa [state] using hw)
  have he : afterTake (state regs frame w) 106 94 0 1 bits rest =
      state (readRegs regs 0 1 none) (Function.update frame 106 rest) {w with node := bits} := by
    simp only [afterTake, state, store_node, hn, List.append_nil,
      update_store_extra _ _ 106 _ (by right; right; right; rfl), update_store_node]
  simpa only [he] using h

theorem peek_extra_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (src : Fin 110) (hsrc : extra src) :
    Eval (peek src) 1 (state regs frame w)
      (state (readRegs regs 0 1 (frame src).head?) frame w) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.peek src 0 1) (state regs frame w))
  simpa only [peek, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    state, store_extra frame w src hsrc] using h

theorem reverse_extra_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (src : Fin 110) (hsrc : extra src) :
    Eval (SubexpFieldCacheControl.reverse src) (9 * (frame src).length + 7)
      (state regs frame w)
      (state (readRegs regs 0 1 none) (Function.update frame src (frame src).reverse) w) := by
  have h107 : src ≠ 107 := by rcases hsrc with rfl | rfl | rfl | rfl <;> decide
  have h108 : src ≠ 108 := by rcases hsrc with rfl | rfl | rfl | rfl <;> decide
  have h := SubexpScanPrimitives.reverse_eval (state regs frame w) src 107 108 0 1
    h107 h108 (by decide) (by decide) (by simp [state]) (by simp [state])
  have he : afterReverse (state regs frame w) src 0 1 =
      state (readRegs regs 0 1 none) (Function.update frame src (frame src).reverse) w := by
    simp only [afterReverse, state, reverseStacks, store_extra frame w src hsrc,
      update_store_extra _ _ src _ hsrc]
  rw [he] at h
  simpa only [SubexpFieldCacheControl.reverse, state, store_extra frame w src hsrc] using h

theorem reverse_inverse_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) :
    Eval (SubexpFieldCacheControl.reverse 98) (9 * w.accumulator.length + 7)
      (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with accumulator := w.accumulator.reverse}) := by
  have h := SubexpScanPrimitives.reverse_eval (state regs frame w) 98 107 108 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state]) (by simp [state])
  have he : afterReverse (state regs frame w) 98 0 1 =
      state (readRegs regs 0 1 none) frame {w with accumulator := w.accumulator.reverse} := by
    simp only [afterReverse, state, reverseStacks, store_accumulator, update_store_accumulator]
  rw [he] at h
  simpa only [SubexpFieldCacheControl.reverse, state, store_accumulator] using h

theorem copy_extra_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (src dst : Fin 110) (hsrc : extra src) (hdst : extra dst)
    (hsd : src ≠ dst) (hz : frame dst = []) :
    Eval (SubexpFieldCacheControl.copy src dst) (7 * (frame src).length + 5)
      (state regs frame w)
      (state (readRegs regs 0 1 none) (Function.update frame dst (frame src)) w) := by
  have hs0 : src ≠ 0 := by rcases hsrc with rfl | rfl | rfl | rfl <;> decide
  have h0d : (0 : Fin 110) ≠ dst := by rcases hdst with rfl | rfl | rfl | rfl <;> decide
  have h := copy_eval (state regs frame w) src dst 0 0 1
    hsd hs0 h0d (by decide) (by simp [state])
  have he : afterCopy (state regs frame w) src dst 0 1 =
      state (readRegs regs 0 1 none) (Function.update frame dst (frame src)) w := by
    simp only [afterCopy, state, copyStacks, store_extra frame w src hsrc,
      store_extra frame w dst hdst, hz, List.append_nil, update_store_extra _ _ dst _ hdst]
  rw [he] at h
  simpa only [SubexpFieldCacheControl.copy, state, store_extra frame w src hsrc] using h

end SubexponentialSAT.SubexpFieldCacheLoop

end OAI.Algorithms
