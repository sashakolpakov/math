import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpHornerSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpHornerInitialize
import OAI.Algorithms.SubexponentialSAT.SubexpHornerCount
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatMul
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd
import OAI.Algorithms.SubexponentialSAT.PolynomialAlgorithm

namespace OAI.Algorithms

/-! A fixed dense Horner evaluator using the actual flat quartic programs.
All coefficients, widths, and loop bounds are runtime stack data. -/

namespace SubexponentialSAT.SubexpHornerMachine

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl
open SubexpLiftRing SubexpQuarticRing

abbrev flat := @SubexpQuarticFlatMul.flat

def mulPorts : Fin 77 ↪ Fin 87 := ⟨Fin.castAdd 10, Fin.castAdd_injective _ _⟩
def addPorts : Fin 20 ↪ Fin 87 :=
  ⟨![0,1,2,3,4,66,6,7,72,80,74,8,9,10,11,12,13,14,15,16], by decide⟩

abbrev multiply : Cmd 8 87 :=
  .call (ProgramLinking.liftProgram SubexpQuarticFlatMul.program id mulPorts)
abbrev add : Cmd 8 87 :=
  .call (ProgramLinking.liftProgram SubexpFlatAdd.program id addPorts)
abbrev iteration : Cmd 8 87 :=
  .seq takeCoefficient (.seq prepareMultiply (.seq multiply add))
abbrev command : Cmd 8 87 :=
  .seq (.call (StackRoutines.reverseProgram 77 83 84 (0 : Fin 8) 1))
    (SubexpHornerControl.command iteration)
abbrev program : Program 8 87 (size command + 1) := compiled command 77 72

theorem flat_eq_encode {B : ℕ} (a : Quad (Word B)) :
    flat a = SubexpFlatAdd.encode a := by
  cases a
  simp [flat, SubexpQuarticFlatMul.flat, SubexpQuarticFlatMul.wordLists,
    FourWordPrograms.flatWords, SubexpFlatAdd.encode, SubexpFlatAdd.flatten,
    SubexpFlatAdd.quadWords, Quad.toFn]

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem multiply_eval (regs : Fin 8 → Bool) (w : Words)
    (t a b : Quad (Word (baseWidth p μ)))
    (hm : w.modulus = M.bits) (hr : w.reduction = flat t)
    (hw : w.width.length = baseWidth p μ)
    (ha : w.left = flat a) (hb : w.right = flat b)
    (hz : w.accumulator = []) (hwork : w.work = []) :
    ∃ n ≤ 400000 * (baseWidth p μ + 1)^2, ∃ regs',
      Eval multiply n (state regs w)
        (state regs' { w with
          left := []
          right := []
          accumulator := flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1 }) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpQuarticFlatMul.program_run p μ M t a b w.width hw regs
  let d := state regs w
  let localIn : State 8 77 :=
    ⟨regs, SubexpQuarticFlatMul.initialStore M.bits w.width t a b⟩
  let localOut : State 8 77 :=
    ⟨rf, SubexpQuarticFlatMul.finalStore M.bits w.width t
      (SubexpPreparedQuartic.binaryMul p μ M t a b).1⟩
  have hin : embedState id mulPorts d localIn = d := by
    apply embedState_eq _ _ Function.injective_id mulPorts.injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [d, localIn, state, store, mulPorts, hm, hr, ha, hb, hz, hwork,
        SubexpQuarticFlatMul.initialStore, SubexpQuarticFlatMul.bankStore,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod]
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intros; rfl
  have hout : embedState id mulPorts d localOut =
      state rf { w with
        left := []
        right := []
        accumulator := flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1 } := by
    apply embedState_eq _ _ Function.injective_id mulPorts.injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [localOut, state, store, mulPorts, hm, hr, hwork,
        SubexpQuarticFlatMul.finalStore, SubexpQuarticFlatMul.bankStore,
        Fin.ext_iff, Fin.coe_ofNat_eq_mod]
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i hi
      have h70 : i ≠ 70 := by intro h; subst i; exact hi ⟨70, rfl⟩
      have h71 : i ≠ 71 := by intro h; subst i; exact hi ⟨71, rfl⟩
      have h72 : i ≠ 72 := by intro h; subst i; exact hi ⟨72, rfl⟩
      simp [state, store, d, h70, h71, h72]
  have hh := eval_call_lifted SubexpQuarticFlatMul.program id mulPorts d
    Function.injective_id mulPorts.injective (a := localIn) (b := localOut) ht
  exact ⟨n, hn, rf, by simpa only [multiply, hin, hout] using hh⟩

theorem add_eval (regs : Fin 8 → Bool) (w : Words)
    (a b : Quad (Word (baseWidth p μ)))
    (hm : w.modulus = M.bits) (hw : w.width.length = baseWidth p μ)
    (ha : w.accumulator = flat a) (hb : w.coefficient = flat b) (hwork : w.work = []) :
    ∃ n ≤ 25000 * (baseWidth p μ + 1)^2, ∃ regs',
      Eval add n (state regs w)
        (state regs' { w with
          coefficient := []
          accumulator := flat (SubexpPreparedQuartic.binaryAdd p μ M a b).1 }) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpFlatAdd.program_runs_uniform p μ M regs a b w.width
    (fun _ => []) hw
  let d := state regs w
  let localIn := SubexpFlatAdd.ready regs M.bits (SubexpFlatAdd.encode a)
    (SubexpFlatAdd.encode b) w.width [] (fun _ => [])
  let localOut := SubexpFlatAdd.ready rf M.bits
    (SubexpFlatAdd.encode (SubexpPreparedQuartic.binaryAdd p μ M a b).1)
    [] w.width [] (fun _ => [])
  have hin : embedState id addPorts d localIn = d := by
    apply embedState_eq _ _ Function.injective_id addPorts.injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [d, localIn, state, store, addPorts, hm, ha, hb, hwork,
        flat_eq_encode, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
        Fin.addCases, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intros; rfl
  have hout : embedState id addPorts d localOut =
      state rf { w with
        coefficient := []
        accumulator := flat (SubexpPreparedQuartic.binaryAdd p μ M a b).1 } := by
    apply embedState_eq _ _ Function.injective_id addPorts.injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [localOut, state, store, addPorts, hm, hwork, flat_eq_encode,
        SubexpFlatAdd.state, SubexpFlatAdd.stacks,
        Fin.addCases, Fin.ext_iff, Fin.coe_ofNat_eq_mod]
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i hi
      have h72 : i ≠ 72 := by intro h; subst i; exact hi ⟨8, rfl⟩
      have h80 : i ≠ 80 := by intro h; subst i; exact hi ⟨9, rfl⟩
      simp [state, store, d, h72, h80]
  have hh := eval_call_lifted SubexpFlatAdd.program id addPorts d
    Function.injective_id addPorts.injective (a := localIn) (b := localOut) ht
  exact ⟨n, hn, rf, by simpa only [add, hin, hout] using hh⟩

def baseWords (t x : Quad (Word (baseWidth p μ))) (width blockWidth : List Bool) : Words where
  modulus := M.bits
  width := width
  reduction := flat t
  stream := []
  point := flat x
  shape := []
  accumulator := []
  blockWidth := blockWidth

theorem iteration_count_eval (t x : Quad (Word (baseWidth p μ)))
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hB : blockWidth.length = 4 * baseWidth p μ)
    (regs : Fin 8 → Bool) (cs : List (Quad (Word (baseWidth p μ))))
    (a c : Quad (Word (baseWidth p μ))) (count : List Bool) :
    ∃ n ≤ 500000 * (baseWidth p μ + 1)^2, ∃ regs',
      Eval iteration n
        (state regs (countedWords flat (baseWords p μ M t x width blockWidth) (c :: cs) a count))
        (state regs' (countedWords flat (baseWords p μ M t x width blockWidth)
          cs (stepValue p μ M t x a c) count)) := by
  let w := {(readyWords flat (baseWords p μ M t x width blockWidth) (c :: cs) a)
    with shape := count}
  let w1 := {w with stream := backward flat cs, coefficient := flat c}
  let w2 := {w1 with accumulator := [], left := flat a, right := flat x}
  let w3 := { w2 with
    left := []
    right := []
    accumulator := flat (SubexpPreparedQuartic.binaryMul p μ M t a x).1 }
  have h1 := takeCoefficient_eval regs w (flat c) (backward flat cs) rfl
    (by simpa [w, readyWords, baseWords] using hB) rfl rfl rfl rfl
  have h2 := prepareMultiply_eval (readRegs regs 0 1 none) w1 rfl rfl rfl
  simp only [StackRoutines.readRegs_reset] at h2
  obtain ⟨nm, hnm, rm, hm⟩ := multiply_eval p μ M (readRegs regs 0 1 none) w2 t a x
    rfl rfl hw rfl rfl rfl rfl
  obtain ⟨na, hna, ra, ha⟩ := add_eval p μ M rm w3
    (SubexpPreparedQuartic.binaryMul p μ M t a x).1 c rfl hw rfl rfl rfl
  have hh := h1.seq (h2.seq (hm.seq ha))
  refine ⟨(23 * (flat c).length + 18) +
      ((6 * (flat a).length + 7 * (flat x).length + 11) + (nm + na)), ?_, ra, ?_⟩
  · simp only [SubexpQuarticFlatMul.flat_length]
    nlinarith [Nat.zero_le (baseWidth p μ), Nat.zero_le ((baseWidth p μ)^2)]
  · simpa only [iteration, w, w1, w2, w3, countedWords, readyWords, baseWords, stepValue,
      StackRoutines.readRegs_reset] using hh

theorem iteration_eval (t x : Quad (Word (baseWidth p μ)))
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hB : blockWidth.length = 4 * baseWidth p μ)
    (regs : Fin 8 → Bool) (cs : List (Quad (Word (baseWidth p μ))))
    (a c : Quad (Word (baseWidth p μ))) :
    ∃ n ≤ 500000 * (baseWidth p μ + 1)^2, ∃ regs',
      Eval iteration n
        (state regs {(readyWords flat (baseWords p μ M t x width blockWidth) (c :: cs) a)
          with shape := List.replicate cs.length false})
        (state regs' (readyWords flat (baseWords p μ M t x width blockWidth)
          cs (stepValue p μ M t x a c))) := by
  simpa only [countedWords, readyWords] using
    iteration_count_eval p μ M t x width blockWidth hw hB regs cs a c
      (List.replicate cs.length false)

def encodePolynomial (P : List (Quad (Word (baseWidth p μ)))) : List Bool := P.flatMap flat

omit [Fact p.Prime] in
theorem encodePolynomial_length (P : List (Quad (Word (baseWidth p μ)))) :
    (encodePolynomial p μ P).length = P.length * (4 * baseWidth p μ) := by
  induction P with
  | nil => simp [encodePolynomial]
  | cons a P ih =>
      simp [encodePolynomial, SubexpQuarticFlatMul.flat_length, Nat.add_mul] at *
      omega

omit [Fact p.Prime] in
theorem reverse_encodePolynomial (P : List (Quad (Word (baseWidth p μ)))) :
    (encodePolynomial p μ P).reverse = backward flat P.reverse := by
  simpa only [encodePolynomial, backward, Function.comp_def] using
    (List.reverse_flatMap (l := P) (f := flat))

def inputWords (t x : Quad (Word (baseWidth p μ))) (width blockWidth : List Bool)
    (P : List (Quad (Word (baseWidth p μ)))) (seed : Quad (Word (baseWidth p μ))) : Words :=
  {readyWords flat (baseWords p μ M t x width blockWidth) P.reverse seed with
    stream := encodePolynomial p μ P}

def sourceBudget (n B : ℕ) : ℕ :=
  9 * (n * (4 * B)) + 7 + (n * (500000 * (B + 1)^2 + 2) + 2) + 1

theorem sourceBudget_le (n B : ℕ) :
    sourceBudget n B ≤ 600000 * (n + 1) * (B + 1)^2 := by
  have hs : B + 1 ≤ (B + 1)^2 := by nlinarith [Nat.zero_le (B^2)]
  have ht : 500000 * (B + 1)^2 + 36 * B + 2 ≤ 599999 * (B + 1)^2 := by omega
  have hn := Nat.mul_le_mul_left n ht
  unfold sourceBudget
  nlinarith [Nat.zero_le (n * (B + 1)^2)]

/-- The finite table is independent of the coefficient count and all ring
parameters. Input stack 77 contains constant-first flat coefficients. -/
theorem program_run (t x : Quad (Word (baseWidth p μ)))
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hB : blockWidth.length = 4 * baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ)))) (seed : Quad (Word (baseWidth p μ)))
    (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn program (sourceBudget P.length (baseWidth p μ))
      ((state regs (inputWords p μ M t x width blockWidth P seed)).withPC (some program.entry))
      ((state rf (readyWords flat (baseWords p μ M t x width blockWidth) []
        (fold (stepValue p μ M t x) P.reverse seed))).withPC none) := by
  let start := state regs (inputWords p μ M t x width blockWidth P seed)
  have hv := reverse_eval start 77 83 84 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [start, inputWords, readyWords, state, store])
    (by simp [start, inputWords, readyWords, state, store])
  have he : afterReverse start 77 0 1 =
      state (readRegs regs 0 1 none)
        (readyWords flat (baseWords p μ M t x width blockWidth) P.reverse seed) := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 77 <;>
        simp [afterReverse, StackRoutines.reverseStacks, start, inputWords, readyWords,
          state, store, hi, reverse_encodePolynomial]
  have hstream : start.stacks 77 = encodePolynomial p μ P := by
    simp [start,inputWords,readyWords,state,store]
  rw [hstream] at hv
  rw [he] at hv
  obtain ⟨n, hn, rf, hr⟩ := command_eval flat (baseWords p μ M t x width blockWidth)
    iteration (stepValue p μ M t x) (500000 * (baseWidth p μ + 1)^2)
    (iteration_eval p μ M t x width blockWidth hw hB) P.reverse seed (readRegs regs 0 1 none)
  have hh : Eval command (9 * (encodePolynomial p μ P).length + 7 + n) start
      (state rf (readyWords flat (baseWords p μ M t x width blockWidth) []
        (fold (stepValue p μ M t x) P.reverse seed))) := by
    simpa only [command, start, state, store, inputWords] using hv.seq hr
  refine ⟨rf, _, ?_, compiled_halt_trace hh 77 72⟩
  simp only [List.length_reverse] at hn
  rw [encodePolynomial_length]
  unfold sourceBudget
  omega

/-- Full primitive execution of dense Horner evaluation, including stream
reversal, every coefficient read, and every quartic add/multiply program. -/
theorem program_primitive (t x : Quad (Word (baseWidth p μ)))
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hB : blockWidth.length = 4 * baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ)))) (seed : Quad (Word (baseWidth p μ)))
    (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * sourceBudget P.length (baseWidth p μ))
      (primitiveCfg program
        ((state regs (inputWords p μ M t x width blockWidth P seed)).withPC (some program.entry)))
      (primitiveCfg program
        ((state rf (readyWords flat (baseWords p μ M t x width blockWidth) []
          (fold (stepValue p μ M t x) P.reverse seed))).withPC none)) := by
  obtain ⟨rf, hr⟩ := program_run p μ M t x width blockWidth hw hB P seed regs
  exact ⟨rf, BitProgram.primitive_execution _ hr⟩

/-- Combined primitive execution and exact polynomial semantics. No scalar
execution oracle appears among the hypotheses: the proof invokes the fixed
quartic multiplication and addition instruction tables above. -/
theorem evaluate_primitive (c : Fin 4 → ZMod (p^μ))
    (t x : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hB : blockWidth.length = 4 * baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ)))) (zero : Quad (Word (baseWidth p μ)))
    (hz : decode p μ c zero = 0) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (output : Quad (Word (baseWidth p μ))),
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * sourceBudget P.length (baseWidth p μ))
        (primitiveCfg program
          ((state regs (inputWords p μ M t x width blockWidth P zero)).withPC (some program.entry)))
        (primitiveCfg program
          ((state rf (readyWords flat (baseWords p μ M t x width blockWidth) [] output)).withPC none)) ∧
      decode p μ c output =
        (PolynomialAlgorithm.denote (P.map (decode p μ c))).eval (decode p μ c x) := by
  obtain ⟨rf, hr⟩ := program_primitive p μ M t x width blockWidth hw hB P zero regs
  exact ⟨rf, fold (stepValue p μ M t x) P.reverse zero, hr,
    output_decode p μ M c t x ht P zero hz⟩

def zeroCode : Quad (Word (baseWidth p μ)) :=
  ⟨SubexpPreparedQuartic.zeroWord p μ, SubexpPreparedQuartic.zeroWord p μ,
    SubexpPreparedQuartic.zeroWord p μ, SubexpPreparedQuartic.zeroWord p μ⟩

omit [Fact p.Prime] in
theorem zeroCode_flat : flat (zeroCode p μ) = List.replicate (4 * baseWidth p μ) false := by
  change List.replicate (baseWidth p μ) false ++
    (List.replicate (baseWidth p μ) false ++
      (List.replicate (baseWidth p μ) false ++ List.replicate (baseWidth p μ) false)) = _
  rw [show 4 * baseWidth p μ = baseWidth p μ +
    (baseWidth p μ + (baseWidth p μ + baseWidth p μ)) by omega]
  simp only [List.replicate_add]

omit [Fact p.Prime] in
theorem zeroCode_decode (c : Fin 4 → ZMod (p^μ)) : decode p μ c (zeroCode p μ) = 0 := by
  simp only [decode, zeroCode, Quad.map, SubexpPreparedQuartic.zeroWord_value,
    quotientDenote_const, map_zero]

abbrev initializedCommand : Cmd 8 87 := .seq SubexpHornerInitialize.command (.call program)
abbrev initializedProgram : Program 8 87 (size initializedCommand + 1) :=
  compiled initializedCommand 77 72

def initialWords (t x : Quad (Word (baseWidth p μ))) (width : List Bool)
    (P : List (Quad (Word (baseWidth p μ)))) : Words :=
  { inputWords p μ M t x width (List.replicate (4 * baseWidth p μ) false) P (zeroCode p μ) with
    accumulator := []
    blockWidth := [] }

def initializedBudget (n B : ℕ) : ℕ := 28 * B + 17 + sourceBudget n B

theorem initializedBudget_le (n B : ℕ) :
    initializedBudget n B ≤ 700000 * (n + 1) * (B + 1)^2 := by
  have hs : B + 1 ≤ (B + 1)^2 := by nlinarith [Nat.zero_le (B^2)]
  have hb : 28 * B + 17 ≤ 100000 * (B + 1)^2 := by omega
  have hn : 100000 * (B + 1)^2 ≤ 100000 * (n + 1) * (B + 1)^2 := by
    exact Nat.mul_le_mul_right _ (by omega)
  calc
    initializedBudget n B ≤ 100000 * (B + 1)^2 +
        600000 * (n + 1) * (B + 1)^2 := Nat.add_le_add hb (sourceBudget_le n B)
    _ ≤ 100000 * (n + 1) * (B + 1)^2 +
        600000 * (n + 1) * (B + 1)^2 := Nat.add_le_add_right hn _
    _ = _ := by ring

/-- Standalone fixed evaluator: zero and coefficient width are constructed
on tape. Only the base-width and coefficient-count counters are inputs. -/
theorem initialized_run (t x : Quad (Word (baseWidth p μ)))
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn initializedProgram (initializedBudget P.length (baseWidth p μ))
      ((state regs (initialWords p μ M t x width P)).withPC (some initializedProgram.entry))
      ((state rf (readyWords flat
        (baseWords p μ M t x width (List.replicate (4 * baseWidth p μ) false)) []
        (fold (stepValue p μ M t x) P.reverse (zeroCode p μ)))).withPC none) := by
  have hi := SubexpHornerInitialize.command_eval regs (initialWords p μ M t x width P)
    rfl rfl rfl rfl
  have hout :
      { initialWords p μ M t x width P with
        accumulator := List.replicate (4 * (initialWords p μ M t x width P).width.length) false
        blockWidth := List.replicate (4 * (initialWords p μ M t x width P).width.length) false } =
      inputWords p μ M t x width (List.replicate (4 * baseWidth p μ) false) P (zeroCode p μ) := by
    simp [initialWords, inputWords, readyWords, baseWords, hw, zeroCode_flat]
  rw [hout] at hi
  obtain ⟨rf, n, hn, ht⟩ := program_run p μ M t x width
    (List.replicate (4 * baseWidth p μ) false) hw (by simp) P (zeroCode p μ)
    (readRegs regs 0 1 none)
  have hh := hi.seq (Eval.call program ht)
  refine ⟨rf, _, ?_, compiled_halt_trace hh 77 72⟩
  change 28 * width.length + 16 + n + 1 ≤ _
  rw [hw]
  unfold initializedBudget
  omega

/-- Source-level call interface for a larger controller. It returns the
actual halting trace and the decoded value of the output in one statement. -/
theorem initialized_run_evaluates (c : Fin 4 → ZMod (p^μ))
    (t x : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (output : Quad (Word (baseWidth p μ))),
      RunsIn initializedProgram (initializedBudget P.length (baseWidth p μ))
        ((state regs (initialWords p μ M t x width P)).withPC (some initializedProgram.entry))
        ((state rf (readyWords flat
          (baseWords p μ M t x width (List.replicate (4 * baseWidth p μ) false)) [] output)).withPC none) ∧
      decode p μ c output =
        (PolynomialAlgorithm.denote (P.map (decode p μ c))).eval (decode p μ c x) := by
  obtain ⟨rf, hr⟩ := initialized_run p μ M t x width hw P regs
  exact ⟨rf, fold (stepValue p μ M t x) P.reverse (zeroCode p μ), hr,
    output_decode p μ M c t x ht P (zeroCode p μ) (zeroCode_decode p μ c)⟩

theorem initialized_evaluates (c : Fin 4 → ZMod (p^μ))
    (t x : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (output : Quad (Word (baseWidth p μ))),
      Computation.RunsIn (primitive initializedProgram).step
        (primitiveOverhead initializedProgram * initializedBudget P.length (baseWidth p μ))
        (primitiveCfg initializedProgram
          ((state regs (initialWords p μ M t x width P)).withPC (some initializedProgram.entry)))
        (primitiveCfg initializedProgram
          ((state rf (readyWords flat
            (baseWords p μ M t x width (List.replicate (4 * baseWidth p μ) false)) [] output)).withPC none)) ∧
      decode p μ c output =
        (PolynomialAlgorithm.denote (P.map (decode p μ c))).eval (decode p μ c x) := by
  obtain ⟨rf, output, hr, hv⟩ := initialized_run_evaluates p μ M c t x ht width hw P regs
  exact ⟨rf, output, BitProgram.primitive_execution _ hr, hv⟩

/-- The same input layout accepts any unary count word, including the
true-bit counters produced by the local CRT correction routines. -/
def inputWordsWithCount (t x : Quad (Word (baseWidth p μ))) (width blockWidth : List Bool)
    (P : List (Quad (Word (baseWidth p μ)))) (seed : Quad (Word (baseWidth p μ)))
    (count : List Bool) : Words :=
  { inputWords p μ M t x width blockWidth P seed with shape := count }

def initialWordsWithCount (t x : Quad (Word (baseWidth p μ))) (width : List Bool)
    (P : List (Quad (Word (baseWidth p μ)))) (count : List Bool) : Words :=
  { initialWords p μ M t x width P with shape := count }

theorem program_run_with_count (t x : Quad (Word (baseWidth p μ)))
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hB : blockWidth.length = 4 * baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ)))) (seed : Quad (Word (baseWidth p μ)))
    (count : List Bool) (hc : count.length = P.length) (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn program (sourceBudget P.length (baseWidth p μ))
      ((state regs (inputWordsWithCount p μ M t x width blockWidth P seed count)).withPC
        (some program.entry))
      ((state rf (readyWords flat (baseWords p μ M t x width blockWidth) []
        (fold (stepValue p μ M t x) P.reverse seed))).withPC none) := by
  let start := state regs (inputWordsWithCount p μ M t x width blockWidth P seed count)
  have hv := reverse_eval start 77 83 84 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [start, inputWordsWithCount, inputWords, readyWords, state, store])
    (by simp [start, inputWordsWithCount, inputWords, readyWords, state, store])
  have he : afterReverse start 77 0 1 =
      state (readRegs regs 0 1 none)
        (countedWords flat (baseWords p μ M t x width blockWidth) P.reverse seed count) := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 77 <;>
        simp [afterReverse, StackRoutines.reverseStacks, start, inputWordsWithCount,
          inputWords, countedWords, readyWords, state, store, hi, reverse_encodePolynomial]
  have hstream : start.stacks 77 = encodePolynomial p μ P := by
    simp [start,inputWordsWithCount,inputWords,readyWords,state,store]
  rw [hstream] at hv
  rw [he] at hv
  obtain ⟨n, hn, rf, hr⟩ := command_count_eval flat (baseWords p μ M t x width blockWidth)
    iteration (stepValue p μ M t x) (500000 * (baseWidth p μ + 1)^2)
    (iteration_count_eval p μ M t x width blockWidth hw hB) P.reverse seed count
    (by simpa using hc) (readRegs regs 0 1 none)
  have hh : Eval command (9 * (encodePolynomial p μ P).length + 7 + n) start
      (state rf (readyWords flat (baseWords p μ M t x width blockWidth) []
        (fold (stepValue p μ M t x) P.reverse seed))) := by
    simpa only [command, start, state, store, inputWordsWithCount, inputWords] using hv.seq hr
  refine ⟨rf, _, ?_, compiled_halt_trace hh 77 72⟩
  simp only [List.length_reverse] at hn
  rw [encodePolynomial_length]
  unfold sourceBudget
  omega

theorem initialized_run_with_count (t x : Quad (Word (baseWidth p μ)))
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ))))
    (count : List Bool) (hc : count.length = P.length) (regs : Fin 8 → Bool) :
    ∃ rf, RunsIn initializedProgram (initializedBudget P.length (baseWidth p μ))
      ((state regs (initialWordsWithCount p μ M t x width P count)).withPC
        (some initializedProgram.entry))
      ((state rf (readyWords flat
        (baseWords p μ M t x width (List.replicate (4 * baseWidth p μ) false)) []
        (fold (stepValue p μ M t x) P.reverse (zeroCode p μ)))).withPC none) := by
  have hi := SubexpHornerInitialize.command_eval regs
    (initialWordsWithCount p μ M t x width P count) rfl rfl rfl rfl
  have hout :
      { initialWordsWithCount p μ M t x width P count with
        accumulator := List.replicate
          (4 * (initialWordsWithCount p μ M t x width P count).width.length) false
        blockWidth := List.replicate
          (4 * (initialWordsWithCount p μ M t x width P count).width.length) false } =
      inputWordsWithCount p μ M t x width (List.replicate (4 * baseWidth p μ) false)
        P (zeroCode p μ) count := by
    simp [initialWordsWithCount, initialWords, inputWordsWithCount, inputWords,
      readyWords, baseWords, hw, zeroCode_flat]
  rw [hout] at hi
  obtain ⟨rf, n, hn, ht⟩ := program_run_with_count p μ M t x width
    (List.replicate (4 * baseWidth p μ) false) hw (by simp) P (zeroCode p μ)
    count hc (readRegs regs 0 1 none)
  have hh := hi.seq (Eval.call program ht)
  refine ⟨rf, _, ?_, compiled_halt_trace hh 77 72⟩
  change 28 * width.length + 16 + n + 1 ≤ _
  rw [hw]
  unfold initializedBudget
  omega

theorem initialized_run_evaluates_with_count (c : Fin 4 → ZMod (p^μ))
    (t x : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ))))
    (count : List Bool) (hc : count.length = P.length) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (output : Quad (Word (baseWidth p μ))),
      RunsIn initializedProgram (initializedBudget P.length (baseWidth p μ))
        ((state regs (initialWordsWithCount p μ M t x width P count)).withPC
          (some initializedProgram.entry))
        ((state rf (readyWords flat
          (baseWords p μ M t x width (List.replicate (4 * baseWidth p μ) false)) [] output)).withPC none) ∧
      decode p μ c output =
        (PolynomialAlgorithm.denote (P.map (decode p μ c))).eval (decode p μ c x) := by
  obtain ⟨rf, hr⟩ := initialized_run_with_count p μ M t x width hw P count hc regs
  exact ⟨rf, fold (stepValue p μ M t x) P.reverse (zeroCode p μ), hr,
    output_decode p μ M c t x ht P (zeroCode p μ) (zeroCode_decode p μ c)⟩

theorem initialized_evaluates_with_count (c : Fin 4 → ZMod (p^μ))
    (t x : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ))))
    (count : List Bool) (hc : count.length = P.length) (regs : Fin 8 → Bool) :
    ∃ (rf : Fin 8 → Bool) (output : Quad (Word (baseWidth p μ))),
      Computation.RunsIn (primitive initializedProgram).step
        (primitiveOverhead initializedProgram * initializedBudget P.length (baseWidth p μ))
        (primitiveCfg initializedProgram
          ((state regs (initialWordsWithCount p μ M t x width P count)).withPC
            (some initializedProgram.entry)))
        (primitiveCfg initializedProgram
          ((state rf (readyWords flat
            (baseWords p μ M t x width (List.replicate (4 * baseWidth p μ) false)) [] output)).withPC none)) ∧
      decode p μ c output =
        (PolynomialAlgorithm.denote (P.map (decode p μ c))).eval (decode p μ c x) := by
  obtain ⟨rf, output, hr, hv⟩ := initialized_run_evaluates_with_count p μ M c t x ht width hw P count hc regs
  exact ⟨rf, output, BitProgram.primitive_execution _ hr, hv⟩

abbrev initializedCallAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 87 ↪ Fin s) : Cmd r s :=
  .call (ProgramLinking.liftProgram initializedProgram registers ports)

/-- Complete Horner execution inside an arbitrary caller frame. Only four
native stacks change: output72, consumed stream77/count79, and generated
coefficient-width counter81. -/
theorem initialized_callAt_eval {r s : ℕ}
    (registers : Fin 8 ↪ Fin r) (ports : Fin 87 ↪ Fin s)
    (c : Fin 4 → ZMod (p^μ)) (t x : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (width : List Bool) (hw : width.length = baseWidth p μ)
    (P : List (Quad (Word (baseWidth p μ))))
    (count : List Bool) (hc : count.length = P.length) (d : State r s)
    (hlocal : ∀ i, d.stacks (ports i) =
      store (initialWordsWithCount p μ M t x width P count) i) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool) (output : Quad (Word (baseWidth p μ))),
      n ≤ initializedBudget P.length (baseWidth p μ) ∧
      Eval (initializedCallAt registers ports) n d
        ⟨Function.extend registers rf d.regs,
          Function.update (Function.update (Function.update (Function.update d.stacks
            (ports 72) (flat output)) (ports 77) []) (ports 79) [])
            (ports 81) (List.replicate (4 * baseWidth p μ) false)⟩ ∧
      decode p μ c output =
        (PolynomialAlgorithm.denote (P.map (decode p μ c))).eval (decode p μ c x) := by
  obtain ⟨rf, output, ⟨n, hn, htrace⟩, hv⟩ := initialized_run_evaluates_with_count
    p μ M c t x ht width hw P count hc (fun i => d.regs (registers i))
  let localIn := state (fun i => d.regs (registers i))
    (initialWordsWithCount p μ M t x width P count)
  let localOut := state rf (readyWords flat
    (baseWords p μ M t x width (List.replicate (4 * baseWidth p μ) false)) [] output)
  have hp : projectState registers ports d = localIn := by
    apply state_ext
    · rfl
    · funext i
      exact hlocal i
  have hrun := eval_call_from_state initializedProgram registers ports d
    registers.injective ports.injective (b := localOut) (by simpa only [hp] using htrace)
  have hchanges : localOut.stacks =
      Function.update (Function.update (Function.update (Function.update localIn.stacks
        72 (flat output)) 77 []) 79 []) 81 (List.replicate (4 * baseWidth p μ) false) := by
    funext i
    by_cases h72 : i = 72 <;> by_cases h77 : i = 77 <;>
      by_cases h79 : i = 79 <;> by_cases h81 : i = 81 <;>
      simp [localOut, localIn, state, store, readyWords, backward, baseWords,
        initialWordsWithCount, initialWords, inputWords,
        h72, h77, h79, h81]
  have hagree : Function.extend ports localIn.stacks d.stacks = d.stacks :=
    SubexpQuarticFlatLift.extend_agree ports localIn.stacks d.stacks hlocal
  have hend : embedState registers ports d localOut =
      (⟨Function.extend registers rf d.regs,
        Function.update (Function.update (Function.update (Function.update d.stacks
          (ports 72) (flat output)) (ports 77) []) (ports 79) [])
          (ports 81) (List.replicate (4 * baseWidth p μ) false)⟩ : State r s) := by
    apply state_ext
    · rfl
    · change Function.extend ports localOut.stacks d.stacks = _
      rw [hchanges, ProgramLinking.extend_update ports.injective,
        ProgramLinking.extend_update ports.injective, ProgramLinking.extend_update ports.injective,
        ProgramLinking.extend_update ports.injective, hagree]
  exact ⟨n, rf, output, hn, by simpa only [initializedCallAt, hend] using hrun, hv⟩

end SubexponentialSAT.SubexpHornerMachine

end OAI.Algorithms
