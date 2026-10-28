import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpWeightRecords
import OAI.Algorithms.SubexponentialSAT.SubexpWeightCode

namespace OAI.Algorithms

/-!
# Fixed-control modular powers for monomial weights

The exponent is an actual little-endian Boolean stack. The fixed controller
zero-tests and decrements that stack, and each iteration invokes the verified
149-label preserving multiplication routine. No exponent is compiled into the
instruction table. Stack 11 is reserved for the serialized support records.
-/

namespace SubexponentialSAT.SubexpWeightControl

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open scoped BigOperators

abbrev Data := SubexponentialSAT.StructuredProgram.State 8 12

/-- Concrete scalar-service ABI. Its execution field is a trace of the supplied
finite table, not a semantic arithmetic instruction. The endpoint module
constructs this record from the verified modular multiplication program. -/
def scalarStacks (acc modulus base : List Bool) : Fin 9 → List Bool :=
  ![acc, [], [], [], [], modulus, [], [], base]

class ScalarService where
  program : Program 8 9 149
  execute : ∀ (regs : Fin 8 → Bool) (input modulus constant : List Bool) (B : ℕ),
    input.length = B → constant.length = B → modulus.length ≤ B + 1 →
    0 < BinaryArithmetic.toNat modulus → BinaryArithmetic.toNat modulus ≤ 2 ^ B →
    ∃ finalRegs output,
      RunsIn program (6010 * (B + 1) ^ 2)
        ⟨some program.entry, regs, scalarStacks input modulus constant⟩
        ⟨none, finalRegs, scalarStacks output modulus constant⟩ ∧
      output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat input * BinaryArithmetic.toNat constant) % BinaryArithmetic.toNat modulus


def servicePort (i : Fin 9) : Fin 12 := ⟨i.val, by omega⟩

theorem servicePort_injective : Function.Injective servicePort := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 12 => k.val) h

def ports : CounterForPrograms.Ports 8 12 where
  register := ⟨fun i => ⟨i.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    exact congrArg (fun k : Fin 8 => k.val) h⟩
  counter := 9
  scratch := 10
  counter_ne_scratch := by decide

abbrev multiply [ScalarService] : Cmd 8 12 :=
  .call (ProgramLinking.liftProgram ScalarService.program id servicePort)

abbrev powerCommand [ScalarService] : Cmd 8 12 := CounterForPrograms.forCmd ports multiply

abbrev powerProgram [ScalarService] : Program 8 12 (size powerCommand + 1) :=
  compiled powerCommand 9 0

theorem powerProgram_labels [ScalarService] : size powerCommand + 1 = 184 := by
  change size (CounterForPrograms.forCmd ports multiply) + 1 = 184
  rw [CounterForPrograms.size_forCmd]

/-- The multiplication ABI, together with the untouched record source. Counter
and scratch stacks are deliberately excluded from the invariant. -/
def Shape (d : Data) (acc modulus base source : List Bool) : Prop :=
  (∀ i : Fin 9, d.stacks (servicePort i) =
    scalarStacks acc modulus base i) ∧ d.stacks 11 = source

def weightStacks (acc modulus base exponent source : List Bool) : Fin 12 → List Bool :=
  ![acc, [], [], [], [], modulus, [], [], base, exponent, [], source]

theorem stacks_shape (regs : Fin 8 → Bool) (acc modulus base exponent source : List Bool) :
    Shape ⟨regs, weightStacks acc modulus base exponent source⟩ acc modulus base source := by
  constructor
  · intro i
    fin_cases i <;> rfl
  · rfl

private theorem port_ne_counter (i : Fin 9) : servicePort i ≠ ports.counter := by
  intro h
  have := congrArg Fin.val h
  simp only [servicePort, ports] at this
  omega

private theorem port_ne_scratch (i : Fin 9) : servicePort i ≠ ports.scratch := by
  intro h
  have := congrArg Fin.val h
  simp only [servicePort, ports] at this
  omega

private theorem outside_service (j : Fin 12) (hj : 9 ≤ j.val) :
    ¬ ∃ i, servicePort i = j := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp only [servicePort] at this
  omega

theorem shape_stable (acc modulus base source : List Bool) (d e : Data)
    (h : CounterForPrograms.OutsideEq ports d e) (hd : Shape d acc modulus base source) :
    Shape e acc modulus base source := by
  constructor
  · intro i
    rw [← h _ (port_ne_counter i) (port_ne_scratch i)]
    exact hd.1 i
  · rw [← h 11 (by decide) (by decide)]
    exact hd.2

private theorem embed_self (d : Data) (acc modulus base source : List Bool)
    (hd : Shape d acc modulus base source) :
    embedState id servicePort d ⟨d.regs, scalarStacks acc modulus base⟩ = d := by
  apply CounterForPrograms.data_ext
  · simp [embedState]
  · funext j
    by_cases hj : j.val < 9
    · let i : Fin 9 := ⟨j.val, hj⟩
      have hi : servicePort i = j := Fin.ext rfl
      rw [← hi, embedState_stack _ _ _ _ servicePort_injective]
      exact (hd.1 i).symm
    · exact embedState_stack_frame _ _ _ _ _ (outside_service j (by omega))

/-- A body execution is obtained from the concrete modular-multiplication
trace; no callback correctness premise is required. -/
theorem multiply_execute [ScalarService] (d : Data) (acc modulus base source : List Bool) (B : ℕ)
    (hd : Shape d acc modulus base source) (ha : acc.length = B) (hb : base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (n : ℕ) (e : Data) (output : List Bool), n ≤ 6010 * (B + 1) ^ 2 ∧ Eval multiply n d e ∧
      Shape e output modulus base source ∧ output.length = B ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat acc * BinaryArithmetic.toNat base) % BinaryArithmetic.toNat modulus ∧
      e.stacks 9 = d.stacks 9 ∧ e.stacks 10 = d.stacks 10 := by
  obtain ⟨rf, output, ⟨n, hn, ht⟩, hlen, hval⟩ :=
    ScalarService.execute d.regs acc modulus base B ha hb hmLength hm hcapacity
  let e := embedState id servicePort d ⟨rf, scalarStacks output modulus base⟩
  have he : Eval multiply n d e := by
    have h := eval_call_lifted ScalarService.program id servicePort d
      Function.injective_id servicePort_injective
      (a := ⟨d.regs, scalarStacks acc modulus base⟩)
      (b := ⟨rf, scalarStacks output modulus base⟩) ht
    rw [embed_self d acc modulus base source hd] at h
    exact h
  refine ⟨n, e, output, hn, he, ?_, hlen, hval, ?_, ?_⟩
  · constructor
    · intro i
      exact embedState_stack _ _ _ _ servicePort_injective i
    · change e.stacks 11 = source
      rw [show e.stacks 11 = d.stacks 11 from
        embedState_stack_frame _ _ _ _ _ (outside_service 11 (by decide))]
      exact hd.2
  · exact embedState_stack_frame _ _ _ _ _ (outside_service 9 (by decide))
  · exact embedState_stack_frame _ _ _ _ _ (outside_service 10 (by decide))

def PowerInvariant (B : ℕ) (initial modulus base source : List Bool) (i : ℕ) (d : Data) : Prop :=
  ∃ acc, acc.length = B ∧
    (BinaryArithmetic.toNat acc : ZMod (BinaryArithmetic.toNat modulus)) =
      (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) * (BinaryArithmetic.toNat base : ZMod (BinaryArithmetic.toNat modulus)) ^ i ∧
    Shape d acc modulus base source

theorem powerInvariant_stable (B : ℕ) (initial modulus base source : List Bool) :
    CounterForPrograms.FrameStable ports (PowerInvariant B initial modulus base source) := by
  intro i d e h hd
  obtain ⟨acc, hlen, hv, hs⟩ := hd
  exact ⟨acc, hlen, hv, shape_stable acc modulus base source d e h hs⟩

theorem power_body_spec [ScalarService] (B : ℕ) (initial modulus base source : List Bool)
    (hb : base.length = B) (hmLength : modulus.length ≤ B + 1)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    CounterForPrograms.BodySpec ports multiply (PowerInvariant B initial modulus base source)
      (fun _ => 6010 * (B + 1) ^ 2) := by
  intro i d hd hs _
  obtain ⟨acc, ha, hv, hd⟩ := hd
  obtain ⟨n, e, output, hn, he, hshape, hlen, hval, hc, hscratch⟩ :=
    multiply_execute d acc modulus base source B hd ha hb hmLength hm hcapacity
  refine ⟨n, e, hn, he, hc, hscratch.trans hs, output, hlen, ?_, hshape⟩
  rw [hval, ZMod.natCast_mod, Nat.cast_mul, hv, pow_succ, mul_assoc]

/-- Full halted execution of the fixed 184-label exponent loop. The record
source, modulus, and base are preserved; only the accumulator and exponent
change. The exponent width and exact value appear in the time bound. -/
theorem power_execute [ScalarService] (d : Data) (initial modulus base source : List Bool) (B : ℕ)
    (hd : Shape d initial modulus base source) (hs : d.stacks 10 = [])
    (ha : initial.length = B) (hb : base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool),
      RunsIn powerProgram
        (BinaryArithmetic.toNat (d.stacks 9) * (6010 * (B + 1) ^ 2) +
          (BinaryArithmetic.toNat (d.stacks 9) + 1) * (16 * (d.stacks 9).length + 16) + 1)
        (d.withPC (some powerProgram.entry)) (e.withPC none) ∧
      Shape e output modulus base source ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) *
          (BinaryArithmetic.toNat base : ZMod (BinaryArithmetic.toNat modulus)) ^ BinaryArithmetic.toNat (d.stacks 9) ∧
      BinaryArithmetic.toNat (e.stacks 9) = 0 ∧ (e.stacks 9).length = (d.stacks 9).length ∧
      e.stacks 10 = [] := by
  have hi : PowerInvariant B initial modulus base source 0 d :=
    ⟨initial, ha, by simp, hd⟩
  obtain ⟨n, e, ht, ⟨output, hlen, hv, hshape⟩, hz, hw, hscratch, hn⟩ :=
    CounterForPrograms.program_correct ports multiply
      (PowerInvariant B initial modulus base source) (fun _ => 6010 * (B + 1) ^ 2)
      (powerInvariant_stable B initial modulus base source)
      (power_body_spec B initial modulus base source hb hmLength hm hcapacity) d hs hi 9 0
  simp only [CounterForPrograms.budgetSum_const, CounterPrograms.value_eq_toNat] at hn hv hz
  exact ⟨e, output, ⟨n + 1, Nat.add_le_add_right hn 1, ht⟩,
    hshape, hlen, hv, hz, hw, hscratch⟩

theorem shape_stacks (d : Data) (acc modulus base source : List Bool)
    (h : Shape d acc modulus base source) (hs : d.stacks 10 = []) :
    d.stacks = weightStacks acc modulus base (d.stacks 9) source := by
  funext j
  fin_cases j
  · exact h.1 0
  · exact h.1 1
  · exact h.1 2
  · exact h.1 3
  · exact h.1 4
  · exact h.1 5
  · exact h.1 6
  · exact h.1 7
  · exact h.1 8
  · rfl
  · exact hs
  · exact h.2

theorem shape_of_stacks (d : Data) (acc modulus base exponent source : List Bool)
    (h : d.stacks = weightStacks acc modulus base exponent source) :
    Shape d acc modulus base source := by
  constructor
  · intro i
    rw [h]
    exact (stacks_shape d.regs acc modulus base exponent source).1 i
  · rw [h]
    rfl

/-- One support record stores the supplied coordinate identifier, scalar
coordinate word, and binary exponent. The two arithmetic fields are framed in
reverse order so the concrete stack parser restores their little-endian order. -/
structure WeightRecord where
  index : List Bool
  base : List Bool
  exponent : List Bool

def payload (r : WeightRecord) : List Bool :=
  Encoding.frame r.index ++ Encoding.frame r.base.reverse ++ Encoding.frame r.exponent.reverse

def encodeRecords : List WeightRecord → List Bool
  | [] => [false]
  | r :: rs => true :: (payload r ++ encodeRecords rs)

def recordValue (m : ℕ) (r : WeightRecord) : ZMod m :=
  (BinaryArithmetic.toNat r.base : ZMod m) ^ BinaryArithmetic.toNat r.exponent

def recordsValue (m : ℕ) (rs : List WeightRecord) : ZMod m :=
  (rs.map (recordValue m)).prod

def powerSteps (B : ℕ) (exponent : List Bool) : ℕ :=
  BinaryArithmetic.toNat exponent * (6010 * (B + 1) ^ 2) +
    (BinaryArithmetic.toNat exponent + 1) * (16 * exponent.length + 16) + 1

def recordSteps (B : ℕ) (r : WeightRecord) : ℕ :=
  5 * r.index.length + 8 * B + 8 * r.exponent.length + 18 + powerSteps B r.exponent

abbrev processRecord [ScalarService] : Cmd 8 12 :=
  .seq SubexpWeightRecords.skipField
    (.seq (SubexpWeightRecords.readField 8 (by decide))
      (.seq (SubexpWeightRecords.readField 9 (by decide))
        (.seq (.call powerProgram)
          (.seq (SubexpWeightRecords.clearField 8) (SubexpWeightRecords.clearField 9)))))

abbrev recordsLoop [ScalarService] : Cmd 8 12 :=
  .while 7 (.seq processRecord SubexpWeightRecords.readTag)

abbrev weightCommand [ScalarService] : Cmd 8 12 := .seq SubexpWeightRecords.readTag recordsLoop

abbrev weightProgram [ScalarService] : Program 8 12 (size weightCommand + 1) := compiled weightCommand 11 0

theorem weightProgram_labels [ScalarService] : size weightCommand + 1 = 219 := by
  simp [size, StructuredProgram.size]

/-- The complete record body reads both fields, executes the actual power
program, and clears its work words for the next record. -/
theorem processRecord_execute [ScalarService] (d : Data) (initial modulus tail : List Bool)
    (r : WeightRecord) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] [] (payload r ++ tail))
    (ha : initial.length = B) (hb : r.base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (n : ℕ) (e : Data) (output : List Bool), n ≤ recordSteps B r ∧ Eval processRecord n d e ∧
      e.stacks = weightStacks output modulus [] [] tail ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) * recordValue (BinaryArithmetic.toNat modulus) r := by
  let t1 := Encoding.frame r.base.reverse ++ Encoding.frame r.exponent.reverse ++ tail
  let t2 := Encoding.frame r.exponent.reverse ++ tail
  obtain ⟨e1, he1, hs1⟩ := SubexpWeightRecords.skipField_execute d r.index t1 (by
    rw [hd]
    simp [weightStacks, payload, t1, List.append_assoc])
  have hh1 : e1.stacks = weightStacks initial modulus [] [] t1 := by
    rw [hs1, hd]
    funext j
    fin_cases j <;> rfl
  obtain ⟨e2, he2, hs2⟩ := SubexpWeightRecords.readField_execute 8 (by decide)
    e1 r.base.reverse t2 (by rw [hh1]; simp [weightStacks, t1, t2, List.append_assoc])
      (by rw [hh1]; rfl)
  have hh2 : e2.stacks = weightStacks initial modulus r.base [] t2 := by
    rw [hs2, hh1, List.reverse_reverse]
    funext j
    fin_cases j <;> rfl
  obtain ⟨e3, he3, hs3⟩ := SubexpWeightRecords.readField_execute 9 (by decide)
    e2 r.exponent.reverse tail (by rw [hh2]; rfl) (by rw [hh2]; rfl)
  have hh3 : e3.stacks = weightStacks initial modulus r.base r.exponent tail := by
    rw [hs3, hh2, List.reverse_reverse]
    funext j
    fin_cases j <;> rfl
  obtain ⟨e4, output, ⟨np, hnp, hp⟩, hshape, hlen, hv, _, hwidth, hscratch⟩ :=
    power_execute e3 initial modulus r.base tail B
      (shape_of_stacks e3 initial modulus r.base r.exponent tail hh3)
      (by rw [hh3]; rfl) ha hb hmLength hm hcapacity
  have hh4 := shape_stacks e4 output modulus r.base tail hshape hscratch
  have hep : e3.stacks 9 = r.exponent := by rw [hh3]; rfl
  rw [hep] at hnp hv hwidth
  obtain ⟨e5, he5, hs5⟩ := SubexpWeightRecords.clearField_execute 8 e4
  have hh5 : e5.stacks = weightStacks output modulus [] (e4.stacks 9) tail := by
    rw [hs5, hh4]
    funext j
    fin_cases j <;> rfl
  obtain ⟨e6, he6, hs6⟩ := SubexpWeightRecords.clearField_execute 9 e5
  have hh6 : e6.stacks = weightStacks output modulus [] [] tail := by
    rw [hs6, hh5]
    funext j
    fin_cases j <;> rfl
  have ht := Eval.seq he1 (Eval.seq he2 (Eval.seq he3
    (Eval.seq (Eval.call powerProgram hp) (Eval.seq he5 he6))))
  refine ⟨_, e6, output, ?_, ht, hh6, hlen, hv⟩
  have he8 : (e4.stacks 8).length = B := by rw [hh4]; exact hb
  have he9 : (e5.stacks 9).length = r.exponent.length := by rw [hh5]; exact hwidth
  simp only [List.length_reverse, hb, he8, he9]
  change np ≤ powerSteps B r.exponent at hnp
  unfold recordSteps
  omega

def recordsFlag : List WeightRecord → Bool
  | [] => false
  | _ :: _ => true

def afterTag : List WeightRecord → List Bool → List Bool
  | [], suffix => suffix
  | r :: rs, suffix => payload r ++ encodeRecords rs ++ suffix

theorem encodeRecords_tag (rs : List WeightRecord) (suffix : List Bool) :
    encodeRecords rs ++ suffix = recordsFlag rs :: afterTag rs suffix := by
  cases rs <;> simp [encodeRecords, recordsFlag, afterTag, List.append_assoc]

def scanSteps (B : ℕ) : List WeightRecord → ℕ
  | [] => 1
  | r :: rs => recordSteps B r + scanSteps B rs + 2

theorem recordsLoop_execute [ScalarService] (rs : List WeightRecord) (d : Data)
    (initial modulus suffix : List Bool) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] [] (afterTag rs suffix))
    (hf : d.regs 7 = recordsFlag rs) (ha : initial.length = B)
    (hb : ∀ r ∈ rs, r.base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (n : ℕ) (e : Data) (output : List Bool), n ≤ scanSteps B rs ∧ Eval recordsLoop n d e ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) * recordsValue (BinaryArithmetic.toNat modulus) rs := by
  induction rs generalizing d initial with
  | nil =>
      refine ⟨1, d, initial, le_rfl, .while_false hf, hd, ha, ?_⟩
      simp [recordsValue]
  | cons r rs ih =>
      obtain ⟨np, ep, middle, hnp, hp, hsp, hlen, hvp⟩ :=
        processRecord_execute d initial modulus (encodeRecords rs ++ suffix) r B
          (by simpa [afterTag, List.append_assoc] using hd) ha
          (hb r (by simp)) hmLength hm hcapacity
      obtain ⟨et, ht, hst, hft⟩ := SubexpWeightRecords.readTag_execute ep
        (recordsFlag rs) (afterTag rs suffix) (by
          rw [hsp]
          exact encodeRecords_tag rs suffix)
      have hdt : et.stacks = weightStacks middle modulus [] [] (afterTag rs suffix) := by
        rw [hst, hsp]
        funext j
        fin_cases j <;> rfl
      obtain ⟨nt, e, output, hnt, he, hs, ho, hv⟩ :=
        ih et middle hdt hft hlen (fun a ha => hb a (by simp [ha]))
      refine ⟨np + 1 + nt + 1, e, output, ?_, .while_true hf (.seq hp ht) he, hs, ho, ?_⟩
      · simp only [scanSteps]
        omega
      · rw [hv, hvp, mul_assoc]
        simp [recordsValue]

/-- Execution of the entire finite weight program on a serialized support
list. The supplied suffix is preserved, and the output is the product of the
coordinate powers times the initial accumulator. -/
theorem weight_execute [ScalarService] (rs : List WeightRecord) (d : Data)
    (initial modulus suffix : List Bool) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] [] (encodeRecords rs ++ suffix))
    (ha : initial.length = B) (hb : ∀ r ∈ rs, r.base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool), RunsIn weightProgram (scanSteps B rs + 2)
        (d.withPC (some weightProgram.entry)) (e.withPC none) ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) * recordsValue (BinaryArithmetic.toNat modulus) rs := by
  obtain ⟨et, ht, hst, hft⟩ := SubexpWeightRecords.readTag_execute d
    (recordsFlag rs) (afterTag rs suffix) (by
      rw [hd]
      exact encodeRecords_tag rs suffix)
  have hdt : et.stacks = weightStacks initial modulus [] [] (afterTag rs suffix) := by
    rw [hst, hd]
    funext j
    fin_cases j <;> rfl
  obtain ⟨n, e, output, hn, he, hs, ho, hv⟩ :=
    recordsLoop_execute rs et initial modulus suffix B hdt hft ha hb hmLength hm hcapacity
  refine ⟨e, output, ⟨1 + n + 1, by omega, ?_⟩, hs, ho, hv⟩
  exact compiled_halt_trace (Eval.seq ht he) 11 0

def exponentTotal (rs : List WeightRecord) : ℕ :=
  (rs.map (fun r => BinaryArithmetic.toNat r.exponent)).sum

theorem recordSteps_le (B I E : ℕ) (r : WeightRecord)
    (hi : r.index.length ≤ I) (he : r.exponent.length ≤ E) :
    recordSteps B r + 2 ≤
      BinaryArithmetic.toNat r.exponent * (6010 * (B + 1) ^ 2 + 16 * E + 16) +
        (5 * I + 8 * B + 24 * E + 37) := by
  have ht := Nat.mul_le_mul_left (BinaryArithmetic.toNat r.exponent + 1)
    (show 16 * r.exponent.length + 16 ≤ 16 * E + 16 by omega)
  unfold recordSteps powerSteps
  nlinarith

theorem scanSteps_le (B I E : ℕ) (rs : List WeightRecord)
    (hi : ∀ r ∈ rs, r.index.length ≤ I) (he : ∀ r ∈ rs, r.exponent.length ≤ E) :
    scanSteps B rs + 2 ≤
      exponentTotal rs * (6010 * (B + 1) ^ 2 + 16 * E + 16) +
        rs.length * (5 * I + 8 * B + 24 * E + 37) + 3 := by
  induction rs with
  | nil => simp [scanSteps, exponentTotal]
  | cons r rs ih =>
      have hr := recordSteps_le B I E r (hi r (by simp)) (he r (by simp))
      have ht := ih (fun a ha => hi a (by simp [ha])) (fun a ha => he a (by simp [ha]))
      simp only [scanSteps, exponentTotal, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul] at *
      omega

/-- Explicit polynomial bound for retained monomials. D, scalar bit width B,
index width I, and exponent width E remain visible parameters. -/
theorem retained_scanSteps_le (D B I E : ℕ) (rs : List WeightRecord)
    (hcount : rs.length ≤ D) (htotal : exponentTotal rs ≤ 2 * D + 1)
    (hi : ∀ r ∈ rs, r.index.length ≤ I) (he : ∀ r ∈ rs, r.exponent.length ≤ E) :
    scanSteps B rs + 2 ≤
      (2 * D + 1) * (6010 * (B + 1) ^ 2 + 16 * E + 16) +
        D * (5 * I + 8 * B + 24 * E + 37) + 3 := by
  have h := scanSteps_le B I E rs hi he
  have h1 := Nat.mul_le_mul_right (6010 * (B + 1) ^ 2 + 16 * E + 16) htotal
  have h2 := Nat.mul_le_mul_right (5 * I + 8 * B + 24 * E + 37) hcount
  omega

/-- The same execution has an actual primitive-machine trace; the compilation
overhead belongs to one fixed finite program, independent of all input data. -/
theorem weight_primitive [ScalarService] (rs : List WeightRecord) (d : Data)
    (initial modulus suffix : List Bool) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] [] (encodeRecords rs ++ suffix))
    (ha : initial.length = B) (hb : ∀ r ∈ rs, r.base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool), Computation.RunsIn (primitive weightProgram).step
        (primitiveOverhead weightProgram * (scanSteps B rs + 2))
        (primitiveCfg weightProgram (d.withPC (some weightProgram.entry)))
        (primitiveCfg weightProgram (e.withPC none)) ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) * recordsValue (BinaryArithmetic.toNat modulus) rs := by
  obtain ⟨e, output, ht, hs, ho, hv⟩ :=
    weight_execute rs d initial modulus suffix B hd ha hb hmLength hm hcapacity
  exact ⟨e, output, BitProgram.primitive_execution _ ht, hs, ho, hv⟩

/-- The serialization relation for supplied support, coordinate, and exponent
arrays. This definition specifies the machine's input bytes; construction of
those bytes by a surrounding program is a separate caller obligation. -/
def recordsFor {D : ℕ} (support : List (Fin D))
    (indices coordinates exponents : Fin D → List Bool) : List WeightRecord :=
  support.map (fun i => ⟨indices i, coordinates i, exponents i⟩)

theorem recordsValue_recordsFor {D : ℕ} (m : ℕ) (support : List (Fin D))
    (indices coordinates exponents : Fin D → List Bool) :
    recordsValue m (recordsFor support indices coordinates exponents) =
      (SubexpWeightCode.weightWithCost (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod m))
        (fun i => BinaryArithmetic.toNat (exponents i)) support).1 := by
  simp [recordsValue, recordsFor, recordValue, List.map_map, Function.comp_def]

theorem recordsValue_coordinateWeight {D : ℕ} (m : ℕ) (support : List (Fin D))
    (hn : support.Nodup) (indices coordinates exponents : Fin D → List Bool) :
    recordsValue m (recordsFor support indices coordinates exponents) =
      Separation.coordinateWeight support.toFinset id (fun i => BinaryArithmetic.toNat (exponents i))
        (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod m)) := by
  rw [recordsValue_recordsFor, SubexpWeightCode.weightWithCost_eq_coordinateWeight _ _ _ hn]

theorem recordsValue_momentWeight {D : ℕ} (m : ℕ) (support : List (Fin D))
    (hn : support.Nodup) (indices coordinates exponents : Fin D → List Bool)
    (a : Fin D →₀ ℕ) (hexp : ∀ i, BinaryArithmetic.toNat (exponents i) = a i)
    (hcover : ∀ i ∈ a.support, i ∈ support) :
    recordsValue m (recordsFor support indices coordinates exponents) =
      Moments.weight a (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod m)) := by
  rw [recordsValue_recordsFor]
  simp only [hexp]
  exact SubexpWeightCode.weightWithCost_eq_momentWeight_of_support _ _ _ hn hcover

theorem retained_recordsFor_bound {D : ℕ} (B I E : ℕ) (support : List (Fin D))
    (hn : support.Nodup) (indices coordinates exponents : Fin D → List Bool)
    (ha : (∑ i, BinaryArithmetic.toNat (exponents i)) ≤ 2 * D + 1)
    (hi : ∀ i ∈ support, (indices i).length ≤ I)
    (he : ∀ i ∈ support, (exponents i).length ≤ E) :
    scanSteps B (recordsFor support indices coordinates exponents) + 2 ≤
      (2 * D + 1) * (6010 * (B + 1) ^ 2 + 16 * E + 16) +
        D * (5 * I + 8 * B + 24 * E + 37) + 3 := by
  apply retained_scanSteps_le
  · simpa [recordsFor] using hn.length_le_card
  · have hsum : (support.map (fun i => BinaryArithmetic.toNat (exponents i))).sum ≤ ∑ i, BinaryArithmetic.toNat (exponents i) := by
      rw [← List.sum_toFinset _ hn]
      exact Finset.sum_le_sum_of_subset support.toFinset.subset_univ
    simpa [exponentTotal, recordsFor, List.map_map, Function.comp_def] using hsum.trans ha
  · intro r hr
    obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hr
    exact hi i hi'
  · intro r hr
    obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hr
    exact he i hi'

/-- Direct machine-to-moment bridge: a unit initial accumulator produces the
actual moment monomial, not merely an abstract callback result. -/
theorem weight_execute_moment [ScalarService] {D : ℕ} (support : List (Fin D)) (hn : support.Nodup)
    (indices coordinates exponents : Fin D → List Bool)
    (a : Fin D →₀ ℕ) (hexp : ∀ i, BinaryArithmetic.toNat (exponents i) = a i)
    (hcover : ∀ i ∈ a.support, i ∈ support)
    (d : Data) (initial modulus suffix : List Bool) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] []
      (encodeRecords (recordsFor support indices coordinates exponents) ++ suffix))
    (ha : initial.length = B) (hunit : (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) = 1)
    (hb : ∀ i ∈ support, (coordinates i).length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool), RunsIn weightProgram
        (scanSteps B (recordsFor support indices coordinates exponents) + 2)
        (d.withPC (some weightProgram.entry)) (e.withPC none) ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        Moments.weight a (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod (BinaryArithmetic.toNat modulus))) := by
  obtain ⟨e, output, ht, hs, ho, hv⟩ := weight_execute
    (recordsFor support indices coordinates exponents) d initial modulus suffix B hd ha
    (by
      intro r hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      exact hb i hi) hmLength hm hcapacity
  refine ⟨e, output, ht, hs, ho, ?_⟩
  rw [hv, hunit, one_mul, recordsValue_momentWeight _ _ hn _ _ _ a hexp hcover]

end SubexponentialSAT.SubexpWeightControl

end OAI.Algorithms
