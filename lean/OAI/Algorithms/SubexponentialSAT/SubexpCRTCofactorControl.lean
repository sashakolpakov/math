import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatData
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Fixed stream and stack control for the scalar CRT cofactor loop.
Arithmetic commands are supplied as finite code; the concrete machine module
instantiates them with the checked negation, power, and multiplication tables.
-/

namespace SubexponentialSAT.SubexpCRTCofactorControl

open BitProgram StructuredCalls StackRoutines SubexpScanPrimitives

abbrev Data := State 8 110

/-- The frame is retained on unused ports. Native arithmetic work ports are
explicitly empty at routine boundaries. -/
structure Words where
  modulus : List Bool
  reduction : List Bool
  width : List Bool
  exponent : List Bool
  minusOne : List Bool
  unit : List Bool
  blockWidth : List Bool
  stream : List Bool
  accumulator : List Bool
  node : List Bool := []
  negative : List Bool := []
  power : List Bool := []
  left : List Bool := []
  right : List Bool := []
  result : List Bool := []

def nativeStore (w : Words) : Fin 77 → List Bool :=
  Function.update (Function.update
    (SubexpQuarticFlatMul.bankStore (fun _ => []) w.modulus w.reduction w.width w.result)
    70 w.left) 71 w.right

def store (frame : Fin 110 → List Bool) (w : Words) (j : Fin 110) : List Bool :=
  if h : j.val < 77 then nativeStore w ⟨j.val, h⟩ else
  if j = 81 then [] else if j = 82 then [] else
  if j = 91 then w.exponent else
  if j = 92 then w.minusOne else
  if j = 93 then w.unit else
  if j = 94 then w.node else
  if j = 95 then w.negative else
  if j = 96 then w.power else
  if j = 98 then w.accumulator else
  if j = 99 then w.stream else
  if j = 104 then w.blockWidth else
  if j = 107 then [] else if j = 108 then [] else frame j

def state (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words) : Data :=
  ⟨regs, store frame w⟩

@[simp] theorem store_zero (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 0 = [] := rfl
@[simp] theorem store_modulus (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 66 = w.modulus := rfl
@[simp] theorem store_left (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 70 = w.left := rfl
@[simp] theorem store_right (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 71 = w.right := rfl
@[simp] theorem store_result (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 72 = w.result := rfl
@[simp] theorem store_reduction (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 73 = w.reduction := rfl
@[simp] theorem store_width (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 74 = w.width := rfl
@[simp] theorem store_counter (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 81 = [] := rfl
@[simp] theorem store_scratch (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 82 = [] := rfl
@[simp] theorem store_exponent (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 91 = w.exponent := rfl
@[simp] theorem store_minusOne (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 92 = w.minusOne := rfl
@[simp] theorem store_unit (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 93 = w.unit := rfl
@[simp] theorem store_node (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 94 = w.node := rfl
@[simp] theorem store_negative (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 95 = w.negative := rfl
@[simp] theorem store_power (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 96 = w.power := rfl
@[simp] theorem store_accumulator (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 98 = w.accumulator := rfl
@[simp] theorem store_stream (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 99 = w.stream := rfl
@[simp] theorem store_blockWidth (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 104 = w.blockWidth := rfl
@[simp] theorem store_takeCounter (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 107 = [] := rfl
@[simp] theorem store_takeScratch (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 108 = [] := rfl

theorem update_store_node (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 94 bits = store frame {w with node := bits} := by
  funext j
  by_cases hj : j = 94
  · subst j; simp
  · simp [store, nativeStore, hj]

theorem update_store_stream (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 99 bits = store frame {w with stream := bits} := by
  funext j
  by_cases hj : j = 99
  · subst j; simp
  · simp [store, nativeStore, hj]

theorem update_store_accumulator (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 98 bits = store frame {w with accumulator := bits} := by
  funext j
  by_cases hj : j = 98
  · subst j; simp
  · simp [store, nativeStore, hj]

theorem update_store_left (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 70 bits = store frame {w with left := bits} := by
  funext j
  by_cases hj : j = 70
  · subst j; simp
  · rw [Function.update_noteq hj]
    by_cases h77 : j.val < 77
    · have h70 : (⟨j.val, h77⟩ : Fin 77) ≠ 70 := by
        intro h; apply hj; apply Fin.ext
        exact congrArg (fun i : Fin 77 => i.val) h
      simp only [store, dite_eq_left h77, nativeStore]
      by_cases h71 : (⟨j.val, h77⟩ : Fin 77) = 71
      · have hj71 : j = (71 : Fin 110) :=
          Fin.ext (congrArg (fun i : Fin 77 => i.val) h71)
        subst j
        rfl
      · simp only [Function.update_noteq h71, Function.update_noteq h70]
    · simp only [store, dite_eq_right h77]

theorem update_store_right (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 71 bits = store frame {w with right := bits} := by
  funext j
  by_cases hj : j = 71
  · subst j; simp
  · rw [Function.update_noteq hj]
    by_cases h77 : j.val < 77
    · have h71 : (⟨j.val, h77⟩ : Fin 77) ≠ 71 := by
        intro h; apply hj; apply Fin.ext
        exact congrArg (fun i : Fin 77 => i.val) h
      simp only [store, dite_eq_left h77, nativeStore, Function.update_noteq h71]
    · simp only [store, dite_eq_right h77]

theorem update_store_result (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 72 bits = store frame {w with result := bits} := by
  funext j
  by_cases hj : j = 72
  · subst j; simp
  · rw [Function.update_noteq hj]
    by_cases h77 : j.val < 77
    · have h72 : (⟨j.val, h77⟩ : Fin 77) ≠ 72 := by
        intro h; apply hj; apply Fin.ext
        exact congrArg (fun i : Fin 77 => i.val) h
      simp only [store, dite_eq_left h77, nativeStore]
      by_cases h71 : (⟨j.val, h77⟩ : Fin 77) = 71
      · have hj71 : j = (71 : Fin 110) :=
          Fin.ext (congrArg (fun i : Fin 77 => i.val) h71)
        subst j
        rfl
      · simp only [Function.update_noteq h71]
        by_cases h70 : (⟨j.val, h77⟩ : Fin 77) = 70
        · have hj70 : j = (70 : Fin 110) :=
            Fin.ext (congrArg (fun i : Fin 77 => i.val) h70)
          subst j
          rfl
        · simp only [Function.update_noteq h70, SubexpQuarticFlatMul.bankStore,
            ite_eq_right h72]
    · simp only [store, dite_eq_right h77]

def mulPorts : Fin 77 ↪ Fin 110 :=
  ⟨Fin.castAdd 33, Fin.castAdd_injective _ _⟩

def registers : Fin 8 ↪ Fin 8 := ⟨id, Function.injective_id⟩

@[simp] theorem store_native (frame : Fin 110 → List Bool) (w : Words) (i : Fin 77) :
    store frame w (mulPorts i) = nativeStore w i := by
  simp [store, mulPorts]

def negPort (i : Fin 24) : Fin 110 :=
  if i = 4 then 92 else if i = 14 then 66 else if i = 18 then 94 else
  if i = 19 then 95 else if i = 20 then 74 else ⟨i.val, by omega⟩

def negPorts : Fin 24 ↪ Fin 110 := ⟨negPort, by decide⟩

def powerRelabel : Equiv.Perm (Fin 110) :=
  (Equiv.swap 77 95).trans ((Equiv.swap 78 91).trans
    ((Equiv.swap 79 93).trans (Equiv.swap 80 96)))

def powerPorts : Fin 83 ↪ Fin 110 :=
  (⟨Fin.castAdd 27, Fin.castAdd_injective _ _⟩ : Fin 83 ↪ Fin 110).trans
    powerRelabel.toEmbedding

abbrev takeNode : Cmd 8 110 := takeWord 104 107 108 99 94 0 1

theorem takeNode_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (bits rest : List Bool) (hs : w.stream = bits ++ rest)
    (hw : w.blockWidth.length = bits.length) (hn : w.node = []) :
    Eval takeNode (14 * bits.length + 11) (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with stream := rest, node := bits}) := by
  have h := takeWord_eval (state regs frame w) 104 107 108 99 94 0 1
    (by decide) (by decide) bits rest
    (by simpa [state] using hs) (by simp [state]) (by simp [state])
    (by simpa [state] using hw)
  have heq : afterTake (state regs frame w) 99 94 0 1 bits rest =
      state (readRegs regs 0 1 none) frame {w with stream := rest, node := bits} := by
    apply state_ext
    · rfl
    · simp only [afterTake, state, store_node, hn, List.append_nil,
        update_store_stream, update_store_node]
  simpa only [takeNode, heq] using h

/-- Move a word through two reversals, leaving its order unchanged. -/
abbrev move (src dst : Fin 110) : Cmd 8 110 :=
  .seq (.call (transferProgram src 0 (0 : Fin 8) 1))
    (.call (transferProgram 0 dst (0 : Fin 8) 1))

abbrev clear (src : Fin 110) : Cmd 8 110 := .call (clearProgram src (0 : Fin 8) 1)

abbrev iteration (negate power multiply : Cmd 8 110) : Cmd 8 110 :=
  .seq takeNode (.seq negate (.seq power
    (.seq (move 98 70) (.seq (move 96 71) (.seq multiply
      (.seq (move 72 98) (.seq (clear 94) (clear 95))))))))

abbrev peekNodes : Cmd 8 110 := .base (.atom (.peek 99 0 1))

abbrev command (negate power multiply : Cmd 8 110) : Cmd 8 110 :=
  .seq (.call (copyProgram 93 98 0 (0 : Fin 8) 1))
    (.seq peekNodes (.while 1 (.seq (iteration negate power multiply) peekNodes)))

def moved (d : Data) (src dst : Fin 110) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst (d.stacks src)⟩

theorem move_eval (d : Data) (src dst : Fin 110)
    (hs : src ≠ 0) (hd : dst ≠ 0) (hsd : src ≠ dst)
    (hzero : d.stacks 0 = []) (hempty : d.stacks dst = []) :
    Eval (move src dst) (6 * (d.stacks src).length + 6) d (moved d src dst) := by
  have h1 := transfer_eval d src 0 0 1 hs (by decide)
  let middle := afterTransfer d src 0 0 1
  have h2 := transfer_eval middle 0 dst 0 1 hd.symm (by decide)
  have hlen : (middle.stacks 0).length = (d.stacks src).length := by
    simp [middle, afterTransfer, transferStacks, hzero]
  have hend : afterTransfer middle 0 dst 0 1 = moved d src dst := by
    apply state_ext
    · simp [afterTransfer, middle, moved, readRegs_reset]
    · funext j
      by_cases hjd : j = dst
      · subst j
        simp [afterTransfer, middle, moved, transferStacks, hd, hsd.symm, hzero, hempty]
      · by_cases hjs : j = src
        · subst j
          simp [afterTransfer, middle, moved, transferStacks, hs, hsd]
        · by_cases hj0 : j = 0
          · subst j
            simp [afterTransfer, middle, moved, transferStacks, hd.symm, hs.symm, hzero]
          · simp [afterTransfer, middle, moved, transferStacks, hjd, hjs, hj0]
  rw [hend] at h2
  have h := h1.seq h2
  convert h using 1
  simp only [hlen]
  omega

theorem update_store_negative (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 95 bits = store frame {w with negative := bits} := by
  funext j
  by_cases hj : j = 95
  · subst j; simp
  · simp [store, nativeStore, hj]

theorem update_store_power (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 96 bits = store frame {w with power := bits} := by
  funext j
  by_cases hj : j = 96
  · subst j; simp
  · simp [store, nativeStore, hj]


end SubexponentialSAT.SubexpCRTCofactorControl

end OAI.Algorithms
