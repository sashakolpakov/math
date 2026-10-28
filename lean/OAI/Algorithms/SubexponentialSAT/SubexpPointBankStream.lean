import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.DensePolynomialLoop
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Coordinate words to the physical beta-input stream

This fixed program consumes a flat bank of fixed-width scalar coordinates,
calls the actual constant-quartic marshaler for each coordinate, and writes
the ordinary framed list consumed by the beta-input zipper.
-/

namespace SubexponentialSAT.SubexpPointBankStream

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

abbrev Data := State 8 8

def state (regs : Fin 8 → Bool)
    (source width word counter tmp record acc output : List Bool) : Data :=
  ⟨regs, ![source, width, word, counter, tmp, record, acc, output]⟩

def ready (regs : Fin 8 → Bool) (source width acc output : List Bool) : Data :=
  state regs source width [] [] [] [] acc output

def smallRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def marshalPorts : Fin 5 → Fin 8 := ![2, 1, 3, 4, 5]
def writerPorts : Fin 4 → Fin 8 := ![0, 1, 5, 4]

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective _ _
theorem marshalPorts_injective : Function.Injective marshalPorts := by decide
theorem writerPorts_injective : Function.Injective writerPorts := by decide

abbrev marshal : Cmd 8 8 := .call
  (ProgramLinking.liftProgram SubexpQuarticMarshal.program smallRegs marshalPorts)

theorem marshal_eval (regs : Fin 8 → Bool) (source width word acc output : List Bool) :
    ∃ rf, Eval marshal (6 * word.length + 12 * width.length + 15)
      (state regs source width word [] [] [] acc output)
      (state rf source width (SubexpQuarticMarshal.marshalBits word width) [] [] [] acc output) := by
  obtain ⟨rr, ht⟩ := SubexpQuarticMarshal.run (regs ∘ smallRegs) word width
  let d := state regs source width word [] [] [] acc output
  let rf := Function.extend smallRegs rr regs
  have h := eval_call_lifted SubexpQuarticMarshal.program smallRegs marshalPorts d
    smallRegs_injective marshalPorts_injective
    (a := ⟨regs ∘ smallRegs, SubexpQuarticMarshal.stackState word width [] [] []⟩)
    (b := ⟨rr, SubexpQuarticMarshal.stackState
      (SubexpQuarticMarshal.marshalBits word width) width [] [] []⟩) ht
  have ha : embedState smallRegs marshalPorts d
      ⟨regs ∘ smallRegs, SubexpQuarticMarshal.stackState word width [] [] []⟩ = d := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective marshalPorts_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState smallRegs marshalPorts d
      ⟨rr, SubexpQuarticMarshal.stackState
        (SubexpQuarticMarshal.marshalBits word width) width [] [] []⟩ =
      state rf source width (SubexpQuarticMarshal.marshalBits word width) [] [] [] acc output := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective marshalPorts_injective
    · intro i; exact smallRegs_injective.extend_apply rr regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨0, h.symm⟩
      fin_cases i <;> first | contradiction | rfl
  rw [ha, hb] at h
  exact ⟨rf, h⟩

abbrev writer : Cmd 8 8 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram smallRegs writerPorts)

def writerRegs (regs : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update regs 0 true) 1 false

def afterWriter (d : Data) (bits : List Bool) : Data :=
  ⟨writerRegs d.regs, Function.update (Function.update d.stacks 4 []) 5
    (true :: (Encoding.frame bits ++ d.stacks 5))⟩

theorem writer_data_eval (d : Data) (bits : List Bool) (hs : d.stacks 4 = bits.reverse) :
    Eval writer (5 * bits.length + 7) d (afterWriter d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 0) (d.stacks 1) (d.stacks 5) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 0) (d.stacks 1) (true :: (Encoding.frame bits ++ d.stacks 5)) []
  have ha : embedState smallRegs writerPorts d a = d := by
    apply embedState_eq _ _ smallRegs_injective writerPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp [a, writerPorts, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hs]
    · intros; rfl
    · intros; rfl
  have hb : embedState smallRegs writerPorts d b = afterWriter d bits := by
    apply embedState_eq _ _ smallRegs_injective writerPorts_injective
    · intro i
      fin_cases i <;> simp [afterWriter, writerRegs, smallRegs, b,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.triple]
    · intro i
      fin_cases i <;> simp [afterWriter, writerPorts, b,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.quadruple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [afterWriter, writerRegs, h0, h1]
    · intro i hi
      have h4 : i ≠ 4 := fun h => hi ⟨3, h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨2, h.symm⟩
      simp [afterWriter, h4, h5]
  have ht := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 1)
    (d.stacks 5) (d.regs 0) (d.regs 1) (d.regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram smallRegs writerPorts d
    smallRegs_injective writerPorts_injective ht
  change Eval _ _ (embedState _ _ d a) (embedState _ _ d b) at h
  simpa only [writer, ha, hb] using h

abbrev move (src dst : Fin 8) : Cmd 8 8 :=
  .call (StackRoutines.transferProgram src dst 0 1)

def record (word width : List Bool) : List Bool :=
  true :: Encoding.frame (SubexpQuarticMarshal.marshalBits word width)

theorem record_length {B : ℕ} (word width : List Bool)
    (hw : word.length = B) (hwidth : width.length = B) :
    (record word width).length = 8 * B + 2 := by
  simp [record, Encoding.length_frame, SubexpQuarticMarshal.marshalBits, hw, hwidth]
  omega

abbrev one : Cmd 8 8 :=
  .seq (takeWord 1 3 4 0 2 0 1)
    (.seq marshal (.seq (move 2 4) (.seq writer (move 5 6))))

theorem one_eval {B : ℕ} (regs : Fin 8 → Bool)
    (word source width acc output : List Bool) (hw : word.length = B)
    (hwidth : width.length = B) :
    ∃ rf, Eval one (88 * B + 45)
      (ready regs (word ++ source) width acc output)
      (ready rf source width ((record word width).reverse ++ acc) output) := by
  let d := ready regs (word ++ source) width acc output
  have ht := takeWord_eval d 1 3 4 0 2 0 1 (by decide) (by decide)
    word source rfl rfl rfl (hwidth.trans hw.symm)
  have he : afterTake d 0 2 0 1 word source =
      state (readRegs regs 0 1 none) source width word [] [] [] acc output := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTake, d, ready, state]
  rw [he, hw] at ht
  obtain ⟨rm, hm⟩ := marshal_eval (readRegs regs 0 1 none) source width word acc output
  rw [hw, hwidth] at hm
  let bits := SubexpQuarticMarshal.marshalBits word width
  have hbits : bits.length = 4 * B := by
    simp [bits, SubexpQuarticMarshal.marshalBits, hw, hwidth]
    omega
  let a := state rm source width bits [] [] [] acc output
  have hmove := transfer_eval a 2 4 0 1 (by decide) (by decide)
  have ea : afterTransfer a 2 4 0 1 =
      state (readRegs rm 0 1 none) source width [] [] bits.reverse [] acc output := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, a, state, StackRoutines.transferStacks]
  rw [ea] at hmove
  change Eval (move 2 4) (3 * bits.length + 3) a _ at hmove
  rw [hbits] at hmove
  let b := state (readRegs rm 0 1 none) source width [] [] bits.reverse [] acc output
  have hwrite := writer_data_eval b bits rfl
  have eb : afterWriter b bits =
      state (writerRegs (readRegs rm 0 1 none)) source width [] [] []
        (record word width) acc output := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterWriter, b, state, record, bits]
  rw [eb, hbits] at hwrite
  let c := state (writerRegs (readRegs rm 0 1 none)) source width [] [] []
    (record word width) acc output
  have hpack := transfer_eval c 5 6 0 1 (by decide) (by decide)
  have ec : afterTransfer c 5 6 0 1 = ready
      (readRegs (writerRegs (readRegs rm 0 1 none)) 0 1 none)
      source width ((record word width).reverse ++ acc) output := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, c, state, ready, StackRoutines.transferStacks]
  rw [ec] at hpack
  change Eval (move 5 6) (3 * (record word width).length + 3) c _ at hpack
  rw [record_length word width hw hwidth] at hpack
  have h := Eval.seq ht (Eval.seq hm (Eval.seq hmove (Eval.seq hwrite hpack)))
  refine ⟨readRegs (writerRegs (readRegs rm 0 1 none)) 0 1 none, ?_⟩
  convert h using 1
  all_goals omega

abbrev guard : Cmd 8 8 := .base (.atom (.peek 0 0 7))

theorem guard_eval (regs : Fin 8 → Bool) (source width acc output : List Bool) :
    Eval guard 1 (ready regs source width acc output)
      (ready (readRegs regs 0 7 source.head?) source width acc output) := by
  exact Eval.base (.atom _ _)

def body (width : List Bool) : List (List Bool) → List Bool
  | [] => []
  | w :: ws => record w width ++ body width ws

theorem body_length {B : ℕ} (xs : List (Word B)) (width : List Bool)
    (hwidth : width.length = B) :
    (body width (xs.map Subtype.val)).length = xs.length * (8 * B + 2) := by
  induction xs with
  | nil => simp [body]
  | cons x xs ih =>
    simp only [List.map_cons, body, List.length_append, record_length x.val width x.property hwidth,
      ih, List.length_cons]
    ring

theorem body_encode (xs : List (List Bool)) (width : List Bool) :
    body width xs ++ [false] =
      Encoding.encodeList (fun w => SubexpQuarticMarshal.marshalBits w width) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [body, record, List.cons_append, List.append_assoc, ih, Encoding.encodeList]

abbrev loop : Cmd 8 8 := .while 7 (.seq one guard)

theorem loop_eval {B : ℕ} (hB : 0 < B) (xs : List (Word B))
    (regs : Fin 8 → Bool) (width acc output : List Bool) (hwidth : width.length = B)
    (hf : regs 7 = (DensePolynomialLoop.flatten xs).head?.isSome) :
    ∃ rf, Eval loop (xs.length * (88 * B + 47) + 1)
      (ready regs (DensePolynomialLoop.flatten xs) width acc output)
      (ready rf [] width ((body width (xs.map Subtype.val)).reverse ++ acc) output) := by
  induction xs generalizing regs acc with
  | nil =>
    refine ⟨regs, ?_⟩
    have h : Eval loop 1 (ready regs [] width acc output) (ready regs [] width acc output) :=
      .while_false hf
    simpa [DensePolynomialLoop.flatten, body] using h
  | cons x xs ih =>
    have hne := DensePolynomialLoop.flatten_cons_ne_nil hB x xs
    have ht : regs 7 = true := by
      rw [hf]
      exact DensePolynomialLoop.head_isSome_of_ne_nil hne
    obtain ⟨r1, h1⟩ := one_eval regs x.val (DensePolynomialLoop.flatten xs)
      width acc output x.property hwidth
    let r2 := readRegs r1 0 7 (DensePolynomialLoop.flatten xs).head?
    have hg := guard_eval r1 (DensePolynomialLoop.flatten xs) width
      ((record x.val width).reverse ++ acc) output
    have hf2 : r2 7 = (DensePolynomialLoop.flatten xs).head?.isSome := by
      simp [r2, readRegs]
    obtain ⟨rf, hrest⟩ := ih r2 ((record x.val width).reverse ++ acc) hf2
    have h := Eval.while_true ht (Eval.seq h1 hg) hrest
    refine ⟨rf, ?_⟩
    convert h using 1
    · simp only [List.length_cons]; ring
    · simp only [DensePolynomialLoop.flatten, List.map_cons, List.flatten_cons]
    · rw [List.map_cons, body, List.reverse_append, List.append_assoc]

abbrev finish : Cmd 8 8 := .seq (.base (.atom (.set 0 false)))
  (.seq (.base (.atom (.push 6 0))) (move 6 7))

theorem finish_eval (regs : Fin 8 → Bool) (width acc output : List Bool) :
    ∃ rf, Eval finish (3 * acc.length + 8) (ready regs [] width acc output)
      (ready rf [] width [] (acc.reverse ++ [false] ++ output)) := by
  let r1 := Function.update regs 0 false
  have h1 : Eval (.base (.atom (.set 0 false))) 1 (ready regs [] width acc output)
      (ready r1 [] width acc output) := Eval.base (.atom _ _)
  have h2 : Eval (.base (.atom (.push 6 0))) 1 (ready r1 [] width acc output)
      (ready r1 [] width (false :: acc) output) := by
    have h := StructuredProgram.Eval.atom (.push (6 : Fin 8) (0 : Fin 8))
      (ready r1 [] width acc output)
    have he : Function.update (![[ ], width, [], [], [], [], acc, output] : Fin 8 → List Bool)
        6 (false :: acc) = ![[], width, [], [], [], [], false :: acc, output] := by
      funext i; fin_cases i <;> rfl
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, ready, state, r1, he] using h
  have h3 := transfer_eval (ready r1 [] width (false :: acc) output) 6 7 0 1
    (by decide) (by decide)
  have he : afterTransfer (ready r1 [] width (false :: acc) output) 6 7 0 1 =
      ready (readRegs r1 0 1 none) [] width [] (acc.reverse ++ [false] ++ output) := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, ready, state,
        StackRoutines.transferStacks, List.reverse_cons, List.append_assoc]
  have hlen : ((ready r1 [] width (false :: acc) output).stacks 6).length = acc.length + 1 := rfl
  rw [he, hlen] at h3
  refine ⟨readRegs r1 0 1 none, ?_⟩
  have h := Eval.seq h1 (Eval.seq h2 h3)
  simpa only [finish, move,
    show 1 + (1 + (3 * (acc.length + 1) + 3)) = 3 * acc.length + 8 by omega] using h

abbrev command : Cmd 8 8 := .seq guard (.seq loop finish)
def program := compiled command 0 7

theorem program_labels : size command + 1 = 75 := rfl

theorem encode_values {B : ℕ} (xs : List (Word B)) (width : List Bool) :
    Encoding.encodeList (fun w => SubexpQuarticMarshal.marshalBits w width) (xs.map Subtype.val) =
      Encoding.encodeList (fun w : Word B => SubexpQuarticMarshal.marshalBits w.val width) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

theorem program_trace {B : ℕ} (hB : 0 < B) (xs : List (Word B))
    (regs : Fin 8 → Bool) (width suffix : List Bool) (hwidth : width.length = B) :
    ∃ rf, Trace program (xs.length * (112 * B + 53) + 11)
      ((ready regs (DensePolynomialLoop.flatten xs) width [] suffix).withPC (some program.entry))
      ((ready rf [] width []
        (Encoding.encodeList (fun w : Word B => SubexpQuarticMarshal.marshalBits w.val width) xs ++ suffix)).withPC none) := by
  have hg := guard_eval regs (DensePolynomialLoop.flatten xs) width [] suffix
  let rg := readRegs regs 0 7 (DensePolynomialLoop.flatten xs).head?
  obtain ⟨rl, hl⟩ := loop_eval hB xs rg width [] suffix hwidth (by simp [rg, readRegs])
  simp only [List.append_nil] at hl
  obtain ⟨rf, hf⟩ := finish_eval rl width (body width (xs.map Subtype.val)).reverse suffix
  simp only [List.length_reverse, List.reverse_reverse, body_encode] at hf
  rw [encode_values] at hf
  have h := compiled_halt_trace (Eval.seq hg (Eval.seq hl hf)) 0 7
  refine ⟨rf, ?_⟩
  rw [body_length xs width hwidth] at h
  convert h using 1
  all_goals first | rfl | ring

end SubexponentialSAT.SubexpPointBankStream

end OAI.Algorithms
