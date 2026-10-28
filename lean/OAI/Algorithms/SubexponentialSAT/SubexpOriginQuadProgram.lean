import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOriginResidue
import OAI.Algorithms.SubexponentialSAT.SubexpRawWordReduction
import OAI.Algorithms.SubexponentialSAT.SubexpFlatLift

namespace OAI.Algorithms

/-! The existing four-word conversion program also computes residues when
its input width is the target-ring width and its output width is the source
width. This file proves that execution, using actual binary remainder and
normalization for each coordinate. No new arithmetic instruction is added. -/

namespace SubexponentialSAT.SubexpOriginQuadProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing
open SubexpFlatLift (ready state stackArray scalarPorts scalarPorts_injective
  scalarLift liftOne repeatLift coefficientLift flatten quadWords encode wordCost)

private theorem take_state (regs : Fin 8 → Bool)
    (x modulus tail packed sw tw : List Bool) (frame : Fin 6 → List Bool) :
    afterTake (ready regs modulus (x ++ tail) packed sw tw frame) 8 6 0 1 x tail =
      state (readRegs regs 0 1 none) [] modulus x [] tail packed sw tw [] [] frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;> simp [afterTake, ready, state, stackArray, Fin.addCases,
      Fin.coe_ofNat_eq_mod]

private theorem copy_state (regs : Fin 8 → Bool)
    (x modulus tail packed sw tw : List Bool) (frame : Fin 6 → List Bool) :
    afterCopy (state regs [] modulus x [] tail packed sw tw [] [] frame) 11 7 0 1 =
      state (readRegs regs 0 1 none) [] modulus x tw tail packed sw tw [] [] frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;> simp [afterCopy, state, stackArray, Fin.addCases,
      Fin.coe_ofNat_eq_mod, StackRoutines.copyStacks]

private theorem scalar_frame (out raw shape out' raw' shape' modulus tail packed sw tw : List Bool)
    (frame : Fin 6 → List Bool) (i : Fin 20) (h0 : i ≠ 0) (h6 : i ≠ 6) (h7 : i ≠ 7) :
    stackArray out modulus raw shape tail packed sw tw [] [] frame i =
      stackArray out' modulus raw' shape' tail packed sw tw [] [] frame i := by
  have hu (a b c : List Bool) : stackArray a modulus b c tail packed sw tw [] [] frame =
      Function.update (Function.update (Function.update
        (stackArray [] modulus [] [] tail packed sw tw [] [] frame) 0 a) 6 b) 7 c := by
    funext j
    simp only [stackArray, Function.update_apply]
    refine Fin.addCases (m := 14) (n := 6) ?_ ?_ j
    · intro k; fin_cases k <;> simp [Fin.addCases, Fin.coe_ofNat_eq_mod]
    · intro k
      have hzero : Fin.natAdd 14 k ≠ (0 : Fin 20) := by
        intro h; have hv := congrArg Fin.val h; change 14 + k.val = 0 at hv; omega
      have hsix : Fin.natAdd 14 k ≠ (6 : Fin 20) := by
        intro h; have hv := congrArg Fin.val h; change 14 + k.val = 6 at hv; omega
      have hseven : Fin.natAdd 14 k ≠ (7 : Fin 20) := by
        intro h; have hv := congrArg Fin.val h; change 14 + k.val = 7 at hv; omega
      simp [Fin.addCases, hzero, hsix, hseven]
  rw [hu out raw shape, hu out' raw' shape']
  simp only [Function.update_apply, h0, h6, h7, ite_false]

private theorem transfer_word (regs : Fin 8 → Bool)
    (out modulus tail packed sw tw : List Bool) (frame : Fin 6 → List Bool) :
    afterTransfer (state regs out modulus [] [] tail packed sw tw [] [] frame) 0 9 0 1 =
      ready (readRegs regs 0 1 none) modulus tail (out.reverse ++ packed) sw tw frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;> simp [afterTransfer, ready, state, stackArray, Fin.addCases,
      Fin.coe_ofNat_eq_mod, StackRoutines.transferStacks]

private theorem transfer_result (regs : Fin 8 → Bool)
    (out modulus sw tw : List Bool) (frame : Fin 6 → List Bool) :
    afterTransfer (ready regs modulus [] out.reverse sw tw frame) 9 8 0 1 =
      ready (readRegs regs 0 1 none) modulus out [] sw tw frame := by
  apply state_ext
  · rfl
  · funext i
    fin_cases i <;> simp [afterTransfer, ready, state, stackArray, Fin.addCases,
      Fin.coe_ofNat_eq_mod, StackRoutines.transferStacks]

theorem scalar_eval (regs : Fin 8 → Bool)
    (x modulus tail packed sw tw : List Bool) (frame : Fin 6 → List Bool) :
    ∃ n ≤ SubexpWordLiftMachine.runtimeBound x.length tw.length modulus.length,
      ∃ rf, Eval scalarLift n
        (state regs [] modulus x tw tail packed sw tw [] [] frame)
        (state rf (SubexpOriginResidue.bits tw modulus x) modulus [] []
          tail packed sw tw [] [] frame) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpRawWordReduction.run regs modulus x tw
  let a := SubexpRawWordReduction.inputState regs modulus x tw
  let b := SubexpRawWordReduction.outputState rf modulus (SubexpOriginResidue.bits tw modulus x)
  let d := state regs [] modulus x tw tail packed sw tw [] [] frame
  have ha : embedState id scalarPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scalarPorts_injective
    · intros; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState id scalarPorts d b =
      state rf (SubexpOriginResidue.bits tw modulus x) modulus [] []
        tail packed sw tw [] [] frame := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scalarPorts_injective
    · intros; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [scalarPorts] using h.symm⟩
      have h6 : i ≠ 6 := fun h => hi ⟨6, by simpa [scalarPorts] using h.symm⟩
      have h7 : i ≠ 7 := fun h => hi ⟨7, by simpa [scalarPorts] using h.symm⟩
      exact scalar_frame _ _ _ _ _ _ _ _ _ _ _ frame i h0 h6 h7
  have h := eval_call_lifted SubexpWordLiftMachine.program id scalarPorts d
    Function.injective_id scalarPorts_injective (a := a) (b := b) ht
  exact ⟨n, hn, rf, by simpa only [scalarLift, ha, hb] using h⟩

variable (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
variable {B : ℕ} (width : List Bool) (hw : width.length = baseWidth p 1)

omit [Fact p.Prime] in
theorem one_eval (regs : Fin 8 → Bool) (x : Word B)
    (tail packed inputWidth : List Bool) (frame : Fin 6 → List Bool)
    (hB : inputWidth.length = B) :
    ∃ n ≤ wordCost B (baseWidth p 1) M.bits.length, ∃ rf,
      Eval liftOne n (ready regs M.bits (x.val ++ tail) packed inputWidth width frame)
        (ready rf M.bits tail
          ((SubexpOriginResidue.word p M width hw x).val.reverse ++ packed) inputWidth width frame) := by
  let r1 := readRegs regs 0 1 none
  let d0 := ready regs M.bits (x.val ++ tail) packed inputWidth width frame
  let d1 := state r1 [] M.bits x.val [] tail packed inputWidth width [] [] frame
  have h1 : Eval (takeWord 10 12 13 8 6 0 1) (14 * B + 11) d0 d1 := by
    have h := takeWord_eval d0 10 12 13 8 6 0 1 (by decide) (by decide)
      x.val tail rfl rfl rfl (hB.trans x.property.symm)
    have he : afterTake d0 8 6 0 1 x.val tail = d1 :=
      take_state regs x.val M.bits tail packed inputWidth width frame
    simpa only [x.property, he] using h
  let d2 := state r1 [] M.bits x.val width tail packed inputWidth width [] [] frame
  have h2 : Eval (.call (StackRoutines.copyProgram 11 7 13 (0 : Fin 8) 1))
      (7 * baseWidth p 1 + 5) d1 d2 := by
    have h := copy_eval d1 11 7 13 0 1 (by decide) (by decide) (by decide) (by decide) rfl
    have he : afterCopy d1 11 7 0 1 = d2 := by
      simpa only [d1, d2, r1, StackRoutines.readRegs_reset] using
        copy_state r1 x.val M.bits tail packed inputWidth width frame
    have hl : (d1.stacks 11).length = baseWidth p 1 := hw
    simpa only [he, hl] using h
  obtain ⟨n, hn, r2, h3⟩ := scalar_eval r1 x.val M.bits tail packed inputWidth width frame
  let y := SubexpOriginResidue.word p M width hw x
  let d3 := state r2 y.val M.bits [] [] tail packed inputWidth width [] [] frame
  have h4 : Eval (.call (StackRoutines.transferProgram 0 9 (0 : Fin 8) 1))
      (3 * baseWidth p 1 + 3) d3
      (ready (readRegs r2 0 1 none) M.bits tail (y.val.reverse ++ packed) inputWidth width frame) := by
    have h := transfer_eval d3 0 9 0 1 (by decide) (by decide)
    have he : afterTransfer d3 0 9 0 1 =
        ready (readRegs r2 0 1 none) M.bits tail (y.val.reverse ++ packed) inputWidth width frame :=
      transfer_word r2 y.val M.bits tail packed inputWidth width frame
    have hl : (d3.stacks 0).length = baseWidth p 1 := y.property
    simpa only [he, hl] using h
  refine ⟨(14 * B + 11) + (7 * baseWidth p 1 + 5 + (n + (3 * baseWidth p 1 + 3))),
    ?_, readRegs r2 0 1 none, h1.seq (h2.seq (h3.seq h4))⟩
  rw [x.property, hw] at hn
  unfold wordCost
  omega

omit [Fact p.Prime] in
theorem repeat_eval (regs : Fin 8 → Bool) (xs : List (Word B))
    (packed inputWidth : List Bool) (frame : Fin 6 → List Bool) (hB : inputWidth.length = B) :
    ∃ n ≤ xs.length * wordCost B (baseWidth p 1) M.bits.length, ∃ rf,
      Eval (repeatLift xs.length) n
        (ready regs M.bits (flatten xs) packed inputWidth width frame)
        (ready rf M.bits []
          ((flatten (xs.map (SubexpOriginResidue.word p M width hw))).reverse ++ packed)
          inputWidth width frame) := by
  induction xs generalizing regs packed with
  | nil =>
      exact ⟨0, by simp, regs, by simpa [repeatLift, flatten] using
        (Eval.base (StructuredProgram.Eval.skip (ready regs M.bits [] packed inputWidth width frame)))⟩
  | cons x xs ih =>
      obtain ⟨n, hn, r1, h1⟩ := one_eval p M width hw regs x (flatten xs) packed inputWidth frame hB
      obtain ⟨m, hm, rf, h2⟩ := ih r1 ((SubexpOriginResidue.word p M width hw x).val.reverse ++ packed)
      refine ⟨n + m, ?_, rf, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · simpa [repeatLift, flatten, List.reverse_append, List.append_assoc] using h1.seq h2

abbrev program := SubexpFlatLift.program

def cost (inputWidth outputWidth modulusWidth : ℕ) : ℕ :=
  4 * wordCost inputWidth outputWidth modulusWidth + 12 * outputWidth + 4

omit [Fact p.Prime] in
theorem program_runs (regs : Fin 8 → Bool) (a : Quad (Word B))
    (inputWidth : List Bool) (frame : Fin 6 → List Bool) (hB : inputWidth.length = B) :
    ∃ rf, RunsIn program (cost B (baseWidth p 1) M.bits.length)
      ((ready regs M.bits (encode a) [] inputWidth width frame).withPC (some program.entry))
      ((ready rf M.bits (encode (SubexpOriginResidue.quad p M width hw a)) []
        inputWidth width frame).withPC none) := by
  obtain ⟨n, hn, r1, h1⟩ := repeat_eval p M width hw regs (quadWords a) [] inputWidth frame hB
  have hmap : (quadWords a).map (SubexpOriginResidue.word p M width hw) =
      quadWords (SubexpOriginResidue.quad p M width hw a) := rfl
  rw [hmap, List.append_nil] at h1
  let out := encode (SubexpOriginResidue.quad p M width hw a)
  let d := ready r1 M.bits [] out.reverse inputWidth width frame
  have h2 := transfer_eval d 9 8 0 1 (by decide) (by decide)
  have he : afterTransfer d 9 8 0 1 =
      ready (readRegs r1 0 1 none) M.bits out [] inputWidth width frame :=
    transfer_result r1 out M.bits inputWidth width frame
  have hl : (d.stacks 9).length = 4 * baseWidth p 1 := by
    simp [d, out, ready, state, stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod]
  have h2' : Eval (.call (StackRoutines.transferProgram 9 8 (0 : Fin 8) 1))
      (3 * (4 * baseWidth p 1) + 3) d
      (ready (readRegs r1 0 1 none) M.bits out [] inputWidth width frame) := by
    simpa only [he, hl] using h2
  refine ⟨readRegs r1 0 1 none, n + (3 * (4 * baseWidth p 1) + 3) + 1, ?_,
    compiled_halt_trace (h1.seq h2') 8 8⟩
  simp only [quadWords, List.length_cons, List.length_nil] at hn
  unfold cost
  omega

end SubexponentialSAT.SubexpOriginQuadProgram

end OAI.Algorithms
