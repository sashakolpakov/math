import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCofactorMachine
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAddCall
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Concrete weighted accumulation for the scalar CRT reconstruction.
The preserved factor and value occupy 94 and 95; the running sum occupies 98.
Multiplication and addition use their actual fixed instruction tables. -/

namespace SubexponentialSAT.SubexpCRTWeightedMachine

open BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing SubexpCRTCofactorControl
open SubexpQuarticFlatMul (flat)

def addPort (i : Fin 20) : Fin 110 :=
  if i = 5 then 66 else if i = 8 then 98 else if i = 9 then 72 else
  if i = 10 then 74 else ⟨i.val, by omega⟩

def addPorts : Fin 20 ↪ Fin 110 := ⟨addPort, by decide⟩

abbrev add : Cmd 8 110 := SubexpFlatAddCall.callAt registers addPorts

abbrev prepareProduct : Cmd 8 110 :=
  .seq (.call (copyProgram 94 70 0 (0 : Fin 8) 1))
    (.call (copyProgram 95 71 0 (0 : Fin 8) 1))

abbrev command : Cmd 8 110 :=
  .seq prepareProduct (.seq SubexpCRTCofactorMachine.multiply add)

abbrev program : Program 8 110 (size command + 1) := compiled command 94 98

theorem encode_eq_flat {B : ℕ} (a : Quad (Word B)) : SubexpFlatAdd.encode a = flat a := by
  simp [SubexpFlatAdd.encode, SubexpFlatAdd.flatten, SubexpFlatAdd.quadWords,
    SubexpQuarticFlatMul.flat, SubexpQuarticFlatMul.wordLists,
    FourWordPrograms.flatWords, Quad.toFn]

theorem prepareProduct_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (hl : w.left = []) (hr : w.right = []) :
    Eval prepareProduct (7 * w.node.length + 7 * w.negative.length + 10)
      (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with left := w.node, right := w.negative}) := by
  have h1 := copy_eval (state regs frame w) 94 70 0 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  let w1 : Words := {w with left := w.node}
  have e1 : afterCopy (state regs frame w) 94 70 0 1 =
      state (readRegs regs 0 1 none) frame w1 := by
    simp only [afterCopy, state, copyStacks, store_node, store_left, hl,
      List.append_nil, update_store_left, w1]
  rw [e1] at h1
  have h2 := copy_eval (state (readRegs regs 0 1 none) frame w1) 95 71 0 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have e2 : afterCopy (state (readRegs regs 0 1 none) frame w1) 95 71 0 1 =
      state (readRegs regs 0 1 none) frame {w with left := w.node, right := w.negative} := by
    simp only [afterCopy, state, copyStacks, store_negative, store_right, w1, hr,
      List.append_nil, update_store_right, readRegs_reset]
  rw [e2] at h2
  have hh := h1.seq h2
  convert hh using 1
  simp only [state, store_node, store_negative, w1]
  omega

theorem add_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (a b : Quad (Word (baseWidth p μ)))
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words)
    (hm : w.modulus = M.bits) (ha : w.accumulator = flat a) (hb : w.result = flat b)
    (hw : w.width.length = baseWidth p μ) :
    ∃ n rf, n ≤ 25000 * (baseWidth p μ + 1)^2 ∧
      Eval add n (state regs frame w)
        (state rf frame {w with
          accumulator := flat (SubexpPreparedQuartic.binaryAdd p μ M a b).1
          result := []}) := by
  have hlocal : ∀ i, (state regs frame w).stacks (addPorts i) =
      (SubexpFlatAdd.ready regs M.bits (SubexpFlatAdd.encode a)
        (SubexpFlatAdd.encode b) w.width [] (fun _ => [])).stacks i := by
    intro i
    fin_cases i <;> simp [state, addPorts, addPort, store, nativeStore,
      SubexpQuarticFlatMul.bankStore, SubexpFlatAdd.ready, SubexpFlatAdd.state,
      SubexpFlatAdd.stacks, Fin.addCases, hm, ha, hb, encode_eq_flat, Fin.coe_ofNat_eq_mod]
  obtain ⟨n, rf, hn, he⟩ := SubexpFlatAddCall.callAt_eval registers addPorts
    p μ M a b w.width hw (state regs frame w) (fun _ => []) hlocal
  refine ⟨n, rf, hn, ?_⟩
  simpa only [add, registers, Function.Embedding.coeFn_mk, ProgramLinking.extend_id, state,
    SubexpFlatAddCall.resultStacks, show addPorts 8 = (98 : Fin 110) from rfl,
    show addPorts 9 = (72 : Fin 110) from rfl, encode_eq_flat,
    update_store_accumulator, update_store_result] using he

def stepValue (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a factor value : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) :=
  (SubexpPreparedQuartic.binaryAdd p μ M a
    (SubexpPreparedQuartic.binaryMul p μ M t factor value).1).1

def runtimeBound (B : ℕ) : ℕ := 425000 * (B + 1)^2 + 56 * B + 11

theorem command_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a factor value : Quad (Word (baseWidth p μ)))
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words)
    (hm : w.modulus = M.bits) (ht : w.reduction = flat t)
    (ha : w.accumulator = flat a) (hf : w.node = flat factor) (hv : w.negative = flat value)
    (hl : w.left = []) (hr : w.right = []) (hz : w.result = [])
    (hw : w.width.length = baseWidth p μ) :
    ∃ n rf, n + 1 ≤ runtimeBound (baseWidth p μ) ∧
      Eval command n (state regs frame w)
        (state rf frame {w with accumulator := flat (stepValue p μ M t a factor value)}) := by
  have hp := prepareProduct_eval regs frame w hl hr
  let wp : Words := {w with left := w.node, right := w.negative}
  let product := (SubexpPreparedQuartic.binaryMul p μ M t factor value).1
  obtain ⟨nm, rm, hnm, hmultiply⟩ := SubexpCRTCofactorMachine.multiply_eval p μ M t factor value
    (readRegs regs 0 1 none) frame wp hm ht hf hv hz hw
  let wm : Words := {wp with left := [], right := [], result := flat product}
  obtain ⟨na, ra, hna, hadd⟩ := add_eval p μ M a product rm frame wm hm ha rfl hw
  refine ⟨7 * w.node.length + 7 * w.negative.length + 10 + (nm + na), ra, ?_, ?_⟩
  · simp only [hf, hv, SubexpQuarticFlatMul.flat_length, runtimeBound]
    omega
  · have hh := hp.seq (hmultiply.seq hadd)
    simpa only [command, wp, wm, stepValue, product, hl, hr, hz] using hh

theorem stepValue_decode (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a factor value : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c) :
    SubexpCRTCofactorMachine.decode p μ c (stepValue p μ M t a factor value) =
      SubexpCRTCofactorMachine.decode p μ c a +
        SubexpCRTCofactorMachine.decode p μ c factor *
        SubexpCRTCofactorMachine.decode p μ c value := by
  simp only [SubexpCRTCofactorMachine.decode, stepValue,
    SubexpPreparedQuartic.binaryAdd_quotient,
    SubexpPreparedQuartic.binaryMul_quotient p μ M c t factor value ht]

abbrev callAt {r s : ℕ} (reg : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s) : Cmd r s :=
  .call (ProgramLinking.liftProgram program reg ports)

/-- The weighted update in a caller's actual stack frame. The factor and
evaluation words are preserved and only the accumulator stack changes. -/
theorem callAt_eval {r s : ℕ} (reg : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a factor value : Quad (Word (baseWidth p μ)))
    (frame : Fin 110 → List Bool) (w : Words)
    (hm : w.modulus = M.bits) (ht : w.reduction = flat t)
    (ha : w.accumulator = flat a) (hf : w.node = flat factor) (hv : w.negative = flat value)
    (hl : w.left = []) (hr : w.right = []) (hz : w.result = [])
    (hw : w.width.length = baseWidth p μ) (d : State r s)
    (hstore : ∀ i, d.stacks (ports i) = store frame w i) :
    ∃ n rf, n ≤ runtimeBound (baseWidth p μ) ∧
      Eval (callAt reg ports) n d
        ⟨Function.extend reg rf d.regs,
          Function.update d.stacks (ports 98) (flat (stepValue p μ M t a factor value))⟩ := by
  obtain ⟨n, rf, hn, he⟩ := command_eval p μ M t a factor value
    (fun i => d.regs (reg i)) frame w hm ht ha hf hv hl hr hz hw
  let localIn := state (fun i => d.regs (reg i)) frame w
  let localOut := state rf frame {w with accumulator := flat (stepValue p μ M t a factor value)}
  have hp : projectState reg ports d = localIn := by
    apply state_ext
    · rfl
    · funext i
      exact hstore i
  have ht' := compiled_halt_trace he 94 98
  have hrun := eval_call_from_state program reg ports d reg.injective ports.injective
    (b := localOut) (by simpa only [program, hp] using ht')
  have hagree : Function.extend ports (store frame w) d.stacks = d.stacks :=
    SubexpQuarticFlatLift.extend_agree ports (store frame w) d.stacks hstore
  have hout : embedState reg ports d localOut =
      (⟨Function.extend reg rf d.regs,
        Function.update d.stacks (ports 98) (flat (stepValue p μ M t a factor value))⟩ :
          State r s) := by
    apply state_ext
    · rfl
    · change Function.extend ports
        (store frame {w with accumulator := flat (stepValue p μ M t a factor value)})
        d.stacks = _
      rw [← update_store_accumulator, ProgramLinking.extend_update ports.injective, hagree]
  exact ⟨n + 1, rf, hn, by simpa only [callAt, hout] using hrun⟩

end SubexponentialSAT.SubexpCRTWeightedMachine

end OAI.Algorithms
