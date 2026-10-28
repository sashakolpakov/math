import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.DyadicWidth
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Actual overflow-controlled enumeration of framed binary tuples

The callback is fixed executable code. Every iteration invokes it and then
invokes the concrete framed odometer, including the final overflow increment.
The number and widths of records are never part of finite control.
-/

namespace SubexponentialSAT.ExecCNFTupleEnumeration

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open ExecCNFTupleOdometer

abbrev Ports := CounterForPrograms.Ports
abbrev Data := StructuredProgram.State

variable {R S : ℕ}

abbrev incrementCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram ExecCNFTupleOdometer.program p.register
    (CounterForPrograms.stackPorts p))

noncomputable def incrementResult (p : Ports R S) (d : Data R S)
    (words : List (List Bool)) : Data R S :=
  CounterForPrograms.install p d false false (bumpWords words).1
    (Encoding.encodeList id (bumpWords words).2) []

theorem increment_eval (p : Ports R S) (words : List (List Bool)) (d : Data R S)
    (hc : d.stacks p.counter = Encoding.encodeList id words) (hs : d.stacks p.scratch = []) :
    ∃ n, n ≤ 7 * (Encoding.encodeList id words).length + 3 ∧
      StructuredCalls.Eval (incrementCmd p) n d (incrementResult p d words) := by
  obtain ⟨n, hn, ht⟩ := ExecCNFTupleOdometer.increment_runs words []
    (d.regs (p.register 0)) (d.regs (p.register 1)) (d.regs (p.register 2))
  have ht' : Trace ExecCNFTupleOdometer.program n
      ((CounterForPrograms.localData (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2)) (Encoding.encodeList id words) []).withPC
          (some ExecCNFTupleOdometer.program.entry))
      ((CounterForPrograms.localData false false (bumpWords words).1
        (Encoding.encodeList id (bumpWords words).2) []).withPC none) := by
    simpa [ExecCNFTupleOdometer.cfg, CounterForPrograms.localData, State.withPC] using ht
  have he := StructuredCalls.eval_call_lifted ExecCNFTupleOdometer.program
    p.register (CounterForPrograms.stackPorts p) d p.register.injective
    (CounterForPrograms.stackPorts p).injective ht'
  change StructuredCalls.Eval (incrementCmd p) n
    (CounterForPrograms.install p d _ _ _ (Encoding.encodeList id words) [])
    (incrementResult p d words) at he
  rw [← hc, ← hs, CounterForPrograms.install_self] at he
  exact ⟨n, hn, he⟩

abbrev advanceCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (incrementCmd p) (.base (.atom (.bnot (p.register 2) (p.register 2))))

noncomputable def advanceResult (p : Ports R S) (d : Data R S)
    (words : List (List Bool)) : Data R S :=
  (Atom.bnot (p.register 2) (p.register 2)).eval (incrementResult p d words)

theorem advance_eval (p : Ports R S) (words : List (List Bool)) (d : Data R S)
    (hc : d.stacks p.counter = Encoding.encodeList id words) (hs : d.stacks p.scratch = []) :
    ∃ n, n ≤ 7 * (Encoding.encodeList id words).length + 4 ∧
      StructuredCalls.Eval (advanceCmd p) n d (advanceResult p d words) := by
  obtain ⟨n, hn, he⟩ := increment_eval p words d hc hs
  exact ⟨n + 1, by omega, .seq he (.base (.atom _ _))⟩

@[simp] theorem advanceResult_flag (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    (advanceResult p d words).regs (p.register 2) = !(bumpWords words).1 := by
  simp [advanceResult, Atom.eval, State.ofCfg, Atom.instr, execInstr,
    incrementResult]

@[simp] theorem advanceResult_counter (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    (advanceResult p d words).stacks p.counter = Encoding.encodeList id (bumpWords words).2 := by
  change (incrementResult p d words).stacks p.counter = _
  simp [incrementResult]

@[simp] theorem advanceResult_scratch (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    (advanceResult p d words).stacks p.scratch = [] := by
  change (incrementResult p d words).stacks p.scratch = _
  simp [incrementResult]

theorem advanceResult_outside (p : Ports R S) (d : Data R S) (words : List (List Bool)) :
    CounterForPrograms.OutsideEq p d (advanceResult p d words) := by
  intro j hc hs
  change d.stacks j = (incrementResult p d words).stacks j
  exact (CounterForPrograms.install_other_stack p d _ _ _ _ _ j hc hs).symm

abbrev startCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .base (.atom (.set (p.register 2) true))

def startResult (p : Ports R S) (d : Data R S) : Data R S :=
  (Atom.set (p.register 2) true).eval d

@[simp] theorem startResult_flag (p : Ports R S) (d : Data R S) :
    (startResult p d).regs (p.register 2) = true := by
  simp [startResult, Atom.eval, State.ofCfg, Atom.instr, execInstr ]

@[simp] theorem startResult_stacks (p : Ports R S) (d : Data R S) :
    (startResult p d).stacks = d.stacks := rfl

abbrev loopCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .while (p.register 2) (.seq body (advanceCmd p))

abbrev enumerate (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .seq (startCmd p) (loopCmd p body)

/-- The log contains the payload rank at every actual callback invocation. -/
inductive Visits (p : Ports R S) (body : StructuredCalls.Cmd R S) (shape : List ℕ) :
    List ℕ → ℕ → Data R S → Data R S → Prop
  | done (d : Data R S) (hf : d.regs (p.register 2) = false) : Visits p body shape [] 1 d d
  | step {words : List (List Bool)} {d e f : Data R S} {nb na nt : ℕ} {ranks : List ℕ}
      (hf : d.regs (p.register 2) = true)
      (hw : words.map List.length = shape)
      (hc : d.stacks p.counter = Encoding.encodeList id words)
      (hb : StructuredCalls.Eval body nb d e)
      (he : e.stacks p.counter = Encoding.encodeList id words)
      (ha : StructuredCalls.Eval (advanceCmd p) na e (advanceResult p e words))
      (tail : Visits p body shape ranks nt (advanceResult p e words) f) :
      Visits p body shape (CounterPrograms.value words.flatten :: ranks) ((nb + na) + nt + 1) d f

theorem Visits.eval {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape ranks : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body shape ranks n d e) :
    StructuredCalls.Eval (loopCmd p body) n d e := by
  induction h with
  | done d hf => exact .while_false hf
  | step hf hw hc hb he ha tail ih => exact .while_true hf (.seq hb ha) ih

/-- The only callback premise is a measured execution of actual fixed code,
preserving the tuple and scratch ports while maintaining its data invariant. -/
abbrev BodySpec (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (shape : List ℕ) (I : Data R S → Prop) (budget : ℕ) : Prop :=
  ∀ (words : List (List Bool)) (d : Data R S), words.map List.length = shape → I d →
    d.stacks p.counter = Encoding.encodeList id words → d.stacks p.scratch = [] →
    ∃ n e, n ≤ budget ∧ StructuredCalls.Eval body n d e ∧
      e.stacks p.counter = Encoding.encodeList id words ∧ e.stacks p.scratch = [] ∧ I e

theorem bumpWords_encoded_length (words : List (List Bool)) :
    (Encoding.encodeList id (bumpWords words).2).length =
      (Encoding.encodeList id words).length := by
  have hlen : (bumpWords words).2.length = words.length := by
    simpa only [List.length_map] using congrArg List.length (bumpWords_lengths words)
  simp only [encoded_length, bumpWords_flatten_length, hlen]

/-- Every remaining payload rank is visited exactly once. The induction is on
the semantic remaining count; that number does not occur in executable code. -/
theorem loop_exists (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (shape : List ℕ) (I : Data R S → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : BodySpec p body shape I budget) (fuel : ℕ) :
    ∀ (words : List (List Bool)) (d : Data R S), words.map List.length = shape → I d →
      d.stacks p.counter = Encoding.encodeList id words → d.stacks p.scratch = [] →
      d.regs (p.register 2) = true →
      CounterPrograms.value words.flatten + fuel = 2 ^ words.flatten.length →
      ∃ n e, Visits p body shape (List.range' (CounterPrograms.value words.flatten) fuel) n d e ∧
        I e ∧ e.regs (p.register 2) = false ∧ e.stacks p.scratch = [] ∧
        n ≤ fuel * (budget + 7 * (Encoding.encodeList id words).length + 5) + 1 := by
  induction fuel with
  | zero =>
    intro words d hshape hi hc hs hf hremaining
    have hlt := value_lt_power_length words.flatten
    omega
  | succ fuel ih =>
    intro words d hshape hi hc hs hf hremaining
    obtain ⟨nb, e, hnb, hbody, he, hes, hei⟩ := spec words d hshape hi hc hs
    obtain ⟨na, hna, hstep⟩ := advance_eval p words e he hes
    have hni : I (advanceResult p e words) :=
      stable 0 e (advanceResult p e words) (advanceResult_outside p e words) hei
    by_cases hz : fuel = 0
    · subst fuel
      have hlast : CounterPrograms.value words.flatten + 1 = 2 ^ words.flatten.length := by
        simpa using hremaining
      have hcarry := (overflow_at_last words hlast).1
      have hfalse : (advanceResult p e words).regs (p.register 2) = false := by
        simp only [advanceResult_flag, hcarry, Bool.not_true]
      have htail : Visits p body shape [] 1 (advanceResult p e words) (advanceResult p e words) :=
        .done _ hfalse
      refine ⟨(nb + na) + 1 + 1, advanceResult p e words, ?_, hni, hfalse,
        advanceResult_scratch p e words, ?_⟩
      · simpa using Visits.step hf hshape hc hbody he hstep htail
      · simp only [ zero_add, one_mul]
        omega
    · have hbefore : CounterPrograms.value words.flatten + 1 < 2 ^ words.flatten.length := by
        omega
      obtain ⟨hcarry, hvalue⟩ := advance_before_last words hbefore
      have htrue : (advanceResult p e words).regs (p.register 2) = true := by
        simp only [advanceResult_flag, hcarry, Bool.not_false]
      have hrem : CounterPrograms.value (bumpWords words).2.flatten + fuel =
          2 ^ (bumpWords words).2.flatten.length := by
        rw [bumpWords_flatten_length, hvalue]
        omega
      obtain ⟨nt, f, ht, hfi, hff, hfs, hbound⟩ := ih (bumpWords words).2
        (advanceResult p e words) ((bumpWords_lengths words).trans hshape) hni
        (advanceResult_counter p e words) (advanceResult_scratch p e words) htrue hrem
      rw [bumpWords_encoded_length] at hbound
      refine ⟨(nb + na) + nt + 1, f, ?_, hfi, hff, hfs, ?_⟩
      · simpa only [List.range'_succ, hvalue] using Visits.step hf hshape hc hbody he hstep ht
      · rw [Nat.succ_mul]
        omega

/-- From zero payloads, the actual callback log is exactly all ranks below
2^B. It includes the callback and overflow increment at the final rank. -/
theorem enumerate_correct (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (shape : List ℕ) (I : Data R S → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : BodySpec p body shape I budget)
    (words : List (List Bool)) (d : Data R S)
    (hshape : words.map List.length = shape) (hi : I d)
    (hc : d.stacks p.counter = Encoding.encodeList id words) (hs : d.stacks p.scratch = [])
    (hz : CounterPrograms.value words.flatten = 0) :
    ∃ n e, StructuredCalls.Eval (enumerate p body) (1 + n) d e ∧
      Visits p body shape (List.range' 0 (2 ^ words.flatten.length)) n (startResult p d) e ∧
      I e ∧ e.regs (p.register 2) = false ∧ e.stacks p.scratch = [] ∧
      1 + n ≤ 2 ^ words.flatten.length *
        (budget + 7 * (Encoding.encodeList id words).length + 5) + 2 := by
  have hstart : StructuredCalls.Eval (startCmd p) 1 d (startResult p d) :=
    .base (.atom _ _)
  have hsi : I (startResult p d) := stable 0 d (startResult p d)
    (fun _ _ _ => rfl) hi
  obtain ⟨n, e, hv, hei, hef, hes, hn⟩ := loop_exists p body shape I budget stable spec
    (2 ^ words.flatten.length) words (startResult p d) hshape hsi
    (by simpa using hc) (by simpa using hs) (startResult_flag p d) (by rw [hz]; omega)
  exact ⟨n, e, .seq hstart hv.eval, by simpa only [hz] using hv,
    hei, hef, hes, by omega⟩

/-- Fixed syntax size: only the chosen callback contributes variable code. -/
@[simp] theorem enumerate_size (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.size (enumerate p body) = StructuredCalls.size body + 21 := by
  simp [
    StructuredCalls.size, StructuredProgram.size]
  omega

abbrev program (p : Ports R S) (body : StructuredCalls.Cmd R S) :=
  StructuredCalls.compiled (enumerate p body) p.counter p.counter

/-- The finite-table compiler adds exactly the final halt to the full trace. -/
theorem program_runs (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (shape : List ℕ) (I : Data R S → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : BodySpec p body shape I budget)
    (words : List (List Bool)) (d : Data R S)
    (hshape : words.map List.length = shape) (hi : I d)
    (hc : d.stacks p.counter = Encoding.encodeList id words) (hs : d.stacks p.scratch = [])
    (hz : CounterPrograms.value words.flatten = 0) :
    ∃ e, I e ∧ RunsIn (program p body)
      (2 ^ words.flatten.length * (budget + 7 * (Encoding.encodeList id words).length + 5) + 3)
      (d.withPC (some (program p body).entry)) (e.withPC none) := by
  obtain ⟨n, e, he, hv, hei, hef, hes, hn⟩ :=
    enumerate_correct p body shape I budget stable spec words d hshape hi hc hs hz
  exact ⟨e, hei, 1 + n + 1, by omega, StructuredCalls.compiled_halt_trace he p.counter p.counter⟩

/-- Equal-width little-endian words are determined by their unsigned values. -/
theorem word_eq_of_length_value {a b : List Bool} (hl : a.length = b.length)
    (hv : CounterPrograms.value a = CounterPrograms.value b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons x xs => simp at hl
  | cons x xs ih =>
    cases b with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length = ys.length := by simpa using hl
      have hxy : x = y := by
        cases x <;> cases y <;> simp [CounterPrograms.value] at hv ⊢ <;> omega
      subst y
      have hv' : CounterPrograms.value xs = CounterPrograms.value ys := by
        cases x <;> simp [CounterPrograms.value] at hv <;> omega
      exact congrArg (List.cons x) (ih hl' hv')

theorem tuple_eq_of_shape_flatten {a b : List (List Bool)}
    (hshape : a.map List.length = b.map List.length) (hflat : a.flatten = b.flatten) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => simp at hshape
  | cons x xs ih =>
    cases b with
    | nil => simp at hshape
    | cons y ys =>
      change x.length :: xs.map List.length = y.length :: ys.map List.length at hshape
      obtain ⟨hl, hrest⟩ := List.cons.inj hshape
      change x ++ xs.flatten = y ++ ys.flatten at hflat
      have hx : x = y := List.append_inj_left hflat hl
      have ht : xs.flatten = ys.flatten := List.append_inj_right hflat hl
      exact congrArg₂ List.cons hx (ih hrest ht)

/-- Fixed component widths and payload rank uniquely identify the tuple. -/
theorem tuple_eq_of_shape_value {a b : List (List Bool)}
    (hshape : a.map List.length = b.map List.length)
    (hv : CounterPrograms.value a.flatten = CounterPrograms.value b.flatten) : a = b := by
  have hl : a.flatten.length = b.flatten.length := by
    simpa only [List.length_flatten] using congrArg List.sum hshape
  exact tuple_eq_of_shape_flatten hshape (word_eq_of_length_value hl hv)

/-- Every logged rank is attached to an actual callback trace at a tuple of
the prescribed shape; this includes candidates that the callback rejects. -/
theorem Visits.hit {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape ranks : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body shape ranks n d e) {rank : ℕ} (hr : rank ∈ ranks) :
    ∃ words a b nb, words.map List.length = shape ∧ CounterPrograms.value words.flatten = rank ∧
      a.stacks p.counter = Encoding.encodeList id words ∧ StructuredCalls.Eval body nb a b := by
  induction h with
  | done d hf => simp at hr
  | @step words d e f nb na nt ranks hf hw hc hb he ha tail ih =>
    rcases List.mem_cons.mp hr with hhead | htail
    · exact ⟨words, d, e, nb, hw, hhead.symm, hc, hb⟩
    · exact ih htail

/-- Completeness for all tuples of this shape, hence also for the increasing
in-range tuples retained by the executable guard. -/
theorem Visits.covers {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body shape (List.range' 0 (2 ^ shape.sum)) n d e)
    (target : List (List Bool)) (ht : target.map List.length = shape) :
    ∃ a b nb, a.stacks p.counter = Encoding.encodeList id target ∧ StructuredCalls.Eval body nb a b := by
  have hlen : target.flatten.length = shape.sum := by
    simpa only [List.length_flatten] using congrArg List.sum ht
  have hb : CounterPrograms.value target.flatten < 2 ^ shape.sum := by
    simpa only [hlen] using value_lt_power_length target.flatten
  have hm : CounterPrograms.value target.flatten ∈ List.range' 0 (2 ^ shape.sum) := by
    simpa only [List.mem_range'_1, Nat.zero_le, zero_add, true_and] using hb
  obtain ⟨words, a, b, nb, hw, hv, hc, he⟩ := h.hit hm
  have hwords : words = target := tuple_eq_of_shape_value (hw.trans ht.symm) hv
  subst words
  exact ⟨a, b, nb, hc, he⟩

/-- A core-selector mask followed by r clause indices is one mixed-width
tuple. The bound applies also to m=0, m=1, and r=0. -/
theorem masked_tuple_count_le (m r k : ℕ) :
    2 ^ (([k] ++ List.replicate r (DyadicWidth.width m)).sum) ≤
      2 ^ k * (2 * (m + 1)) ^ r := by
  have he : ([k] ++ List.replicate r (DyadicWidth.width m)).sum =
      k + DyadicWidth.width m * r := by simp [Nat.mul_comm]
  rw [he, pow_add]
  exact Nat.mul_le_mul_left _ (DyadicWidth.tuple_count_le m r)

/-- Whole enumeration compiles to primitive tape steps with a constant that
depends only on the fixed callback and fixed port assignment. -/
theorem program_primitive (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (shape : List ℕ) (I : Data R S → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : BodySpec p body shape I budget)
    (words : List (List Bool)) (d : Data R S)
    (hshape : words.map List.length = shape) (hi : I d)
    (hc : d.stacks p.counter = Encoding.encodeList id words) (hs : d.stacks p.scratch = [])
    (hz : CounterPrograms.value words.flatten = 0) :
    ∃ e, I e ∧ Computation.RunsIn (primitive (program p body)).step
      (primitiveOverhead (program p body) *
        (2 ^ words.flatten.length * (budget + 7 * (Encoding.encodeList id words).length + 5) + 3))
      (primitiveCfg (program p body) (d.withPC (some (program p body).entry)))
      (primitiveCfg (program p body) (e.withPC none)) := by
  obtain ⟨e, hei, he⟩ := program_runs p body shape I budget stable spec words d hshape hi hc hs hz
  exact ⟨e, hei, primitive_execution _ he⟩

/-- A mathematical witness used for coverage: exactly w little-endian bits.
The executable enumerator does not call this function or decode a rank. -/
def fixedBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => decide (n % 2 = 1) :: fixedBits w (n / 2)

@[simp] theorem fixedBits_length (w n : ℕ) : (fixedBits w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [fixedBits, ih]

theorem fixedBits_value (w n : ℕ) (hn : n < 2 ^ w) :
    CounterPrograms.value (fixedBits w n) = n := by
  induction w generalizing n with
  | zero =>
    simp only [pow_zero] at hn
    have hn0 : n = 0 := by omega
    subst n
    rfl
  | succ w ih =>
    have hhalf : n / 2 < 2 ^ w := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2
      simpa only [pow_succ] using hn
    have hbit : (decide (n % 2 = 1)).toNat = n % 2 := by
      have hmod := Nat.mod_lt n (by omega : 0 < 2)
      by_cases h : n % 2 = 1
      · simp [h]
      · simp [h]
        omega
    simp only [fixedBits, CounterPrograms.value, hbit, ih (n / 2) hhalf]
    exact Nat.mod_add_div n 2

theorem fixedBits_map_shape (w : ℕ) (indices : List ℕ) :
    (indices.map (fixedBits w)).map List.length = List.replicate indices.length w := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp [ih, List.replicate_succ]

/-- Every in-range index list and every k-bit selector mask appears in the
actual callback log. An increasing-index guard therefore loses no valid set. -/
theorem Visits.covers_indices {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {m r k n : ℕ} {d e : Data R S}
    (h : Visits p body ([k] ++ List.replicate r (DyadicWidth.width m))
      (List.range' 0 (2 ^ ([k] ++ List.replicate r (DyadicWidth.width m)).sum)) n d e)
    (mask : List Bool) (hmask : mask.length = k)
    (indices : List ℕ) (hlen : indices.length = r) (hindices : ∀ i ∈ indices, i < m) :
    ∃ target a b nb, target.head? = some mask ∧
      (target.drop 1).map CounterPrograms.value = indices ∧
      a.stacks p.counter = Encoding.encodeList id target ∧ StructuredCalls.Eval body nb a b := by
  let target := mask :: indices.map (fixedBits (DyadicWidth.width m))
  have ht : target.map List.length = [k] ++ List.replicate r (DyadicWidth.width m) := by
    change mask.length :: (indices.map (fixedBits (DyadicWidth.width m))).map List.length =
      k :: List.replicate r (DyadicWidth.width m)
    rw [hmask, fixedBits_map_shape, hlen]
  obtain ⟨a, b, nb, hc, he⟩ := h.covers target ht
  refine ⟨target, a, b, nb, rfl, ?_, hc, he⟩
  change (indices.map (fixedBits (DyadicWidth.width m))).map CounterPrograms.value = indices
  rw [List.map_map]
  calc
    _ = indices.map id := by
      apply List.map_congr_left
      intro i hi
      exact fixedBits_value _ i ((hindices i hi).trans (DyadicWidth.lt_two_pow_width m))
    _ = indices := List.map_id _

@[simp] theorem value_replicate_false (w : ℕ) :
    CounterPrograms.value (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, ih]

/-- The separately implemented zero-tuple constructor satisfies the initial
rank condition even when either dimension is zero. -/
@[simp] theorem zero_tuple_value (r w : ℕ) :
    CounterPrograms.value (List.replicate r (List.replicate w false)).flatten = 0 := by
  simp only [List.flatten_replicate_replicate, value_replicate_false]

/-- Latches outside the three odometer registers survive its entire call. -/
theorem advanceResult_register_frame (p : Ports R S) (d : Data R S)
    (words : List (List Bool)) (i : Fin R) (hi : ¬ ∃ j, p.register j = i) :
    (advanceResult p d words).regs i = d.regs i := by
  have hne : i ≠ p.register 2 := by
    intro h
    exact hi ⟨2, h.symm⟩
  simp only [advanceResult, Atom.eval, State.ofCfg, Atom.instr, execInstr, Function.update_of_ne hne]
  unfold incrementResult CounterForPrograms.install
  exact StructuredCalls.embedState_register_frame _ _ _ _ i hi

theorem startResult_register_frame (p : Ports R S) (d : Data R S)
    (i : Fin R) (hi : i ≠ p.register 2) : (startResult p d).regs i = d.regs i := by
  simp [startResult, Atom.eval, State.ofCfg, Atom.instr, execInstr, hi]

/-- The persistent witness stack is exactly the fold of actual callback
updates. Incrementing the tuple does not modify that stack. -/
theorem Visits.stack_fold {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape ranks : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body shape ranks n d e) (j : Fin S)
    (hc : j ≠ p.counter) (hs : j ≠ p.scratch)
    (update : List Bool → ℕ → List Bool)
    (hb : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → StructuredCalls.Eval body nb a b →
      b.stacks j = update (a.stacks j) (CounterPrograms.value words.flatten)) :
    e.stacks j = ranks.foldl update (d.stacks j) := by
  induction h with
  | done d hf => rfl
  | @step words d a e nb na nt ranks hf hw hd hbody ha hadv tail ih =>
    rw [ih, ← advanceResult_outside p a words j hc hs, hb words d a nb hw hd hbody]
    rfl

/-- Invariant-aware witness folding, for callbacks that need a fixed input
formula or a previously saved valid witness in their correctness statement. -/
theorem Visits.stack_fold_of_invariant {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape ranks : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body shape ranks n d e) (j : Fin S)
    (hc : j ≠ p.counter) (hs : j ≠ p.scratch)
    (update : List Bool → ℕ → List Bool) (P : Data R S → Prop) (hP : P d)
    (hb : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → StructuredCalls.Eval body nb a b → P a →
      P b ∧ b.stacks j = update (a.stacks j) (CounterPrograms.value words.flatten))
    (hn : ∀ words a, P a → P (advanceResult p a words)) :
    P e ∧ e.stacks j = ranks.foldl update (d.stacks j) := by
  induction h with
  | done d hf => exact ⟨hP, rfl⟩
  | @step words d a e nb na nt ranks hf hw hd hbody ha hadv tail ih =>
    obtain ⟨hPa, hstack⟩ := hb words d a nb hw hd hbody hP
    obtain ⟨hPe, hfold⟩ := ih (hn words a hPa)
    refine ⟨hPe, ?_⟩
    rw [hfold, ← advanceResult_outside p a words j hc hs, hstack]
    rfl

/-- The candidate-loop bound after substituting the core-mask/index shape.
All padded or rejected candidates and the terminal increment remain charged. -/
theorem masked_program_runs (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (m r k : ℕ) (I : Data R S → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : BodySpec p body ([k] ++ List.replicate r (DyadicWidth.width m)) I budget)
    (words : List (List Bool)) (d : Data R S)
    (hshape : words.map List.length = [k] ++ List.replicate r (DyadicWidth.width m))
    (hi : I d) (hc : d.stacks p.counter = Encoding.encodeList id words)
    (hs : d.stacks p.scratch = []) (hz : CounterPrograms.value words.flatten = 0) :
    ∃ e, I e ∧ RunsIn (program p body)
      (2 ^ k * (2 * (m + 1)) ^ r *
        (budget + 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12) + 3)
      (d.withPC (some (program p body).entry)) (e.withPC none) := by
  obtain ⟨e, hei, he⟩ := program_runs p body _ I budget stable spec words d hshape hi hc hs hz
  have hlen : words.length = r + 1 := by
    simpa only [List.length_map, List.length_append, List.length_singleton,
      List.length_replicate, Nat.add_comm] using congrArg List.length hshape
  have hbits : words.flatten.length = k + r * DyadicWidth.width m := by
    simpa only [List.length_flatten, List.sum_append, List.sum_singleton,
      List.sum_replicate, smul_eq_mul] using congrArg List.sum hshape
  have hcount : 2 ^ words.flatten.length ≤ 2 ^ k * (2 * (m + 1)) ^ r := by
    have hsum : words.flatten.length = ([k] ++ List.replicate r (DyadicWidth.width m)).sum := by
      simpa only [List.length_flatten] using congrArg List.sum hshape
    rw [hsum]
    exact masked_tuple_count_le m r k
  refine ⟨e, hei, he.mono ?_⟩
  have hbudget : budget + 7 * (Encoding.encodeList id words).length + 5 =
      budget + 14 * (k + r * DyadicWidth.width m) + 14 * (r + 1) + 12 := by
    rw [encoded_length, hlen, hbits]
    ring
  rw [hbudget]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hcount) 3

/-- Invariants needed by semantic callback correctness are retained at the
actual occurrence, rather than erased when extracting a rank witness. -/
theorem Visits.hit_of_invariant {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape ranks : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body shape ranks n d e) (P : Data R S → Prop) (hP : P d)
    (hb : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → StructuredCalls.Eval body nb a b → P a → P b)
    (hn : ∀ words a, P a → P (advanceResult p a words))
    {rank : ℕ} (hr : rank ∈ ranks) :
    ∃ words a b nb, words.map List.length = shape ∧ CounterPrograms.value words.flatten = rank ∧
      a.stacks p.counter = Encoding.encodeList id words ∧ StructuredCalls.Eval body nb a b ∧ P a ∧ P b := by
  induction h with
  | done d hf => simp at hr
  | @step words d a e nb na nt ranks hf hw hc hbody ha hadv tail ih =>
    have hPa := hb words d a nb hw hc hbody hP
    rcases List.mem_cons.mp hr with hhead | htail
    · exact ⟨words, d, a, nb, hw, hhead.symm, hc, hbody, hP, hPa⟩
    · exact ih (hn words a hPa) htail

theorem Visits.covers_of_invariant {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body shape (List.range' 0 (2 ^ shape.sum)) n d e)
    (P : Data R S → Prop) (hP : P d)
    (hb : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → StructuredCalls.Eval body nb a b → P a → P b)
    (hn : ∀ words a, P a → P (advanceResult p a words))
    (target : List (List Bool)) (ht : target.map List.length = shape) :
    ∃ a b nb, a.stacks p.counter = Encoding.encodeList id target ∧
      StructuredCalls.Eval body nb a b ∧ P a ∧ P b := by
  have hlen : target.flatten.length = shape.sum := by
    simpa only [List.length_flatten] using congrArg List.sum ht
  have hbound : CounterPrograms.value target.flatten < 2 ^ shape.sum := by
    simpa only [hlen] using value_lt_power_length target.flatten
  have hm : CounterPrograms.value target.flatten ∈ List.range' 0 (2 ^ shape.sum) := by
    simpa only [List.mem_range'_1, Nat.zero_le, zero_add, true_and] using hbound
  obtain ⟨words, a, b, nb, hw, hv, hc, he, hPa, hPb⟩ := h.hit_of_invariant P hP hb hn hm
  have hwords : words = target := tuple_eq_of_shape_value (hw.trans ht.symm) hv
  subst words
  exact ⟨a, b, nb, hc, he, hPa, hPb⟩

/-- Determinism transfers the invariant in the callback's existential contract
to the actual callback execution recorded by the iterator. -/
theorem BodySpec.preserves {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape : List ℕ} {I : Data R S → Prop} {budget : ℕ}
    (spec : BodySpec p body shape I budget) (words : List (List Bool))
    (a b : Data R S) (nb : ℕ) (hw : words.map List.length = shape) (hI : I a)
    (hc : a.stacks p.counter = Encoding.encodeList id words) (hs : a.stacks p.scratch = [])
    (he : StructuredCalls.Eval body nb a b) : I b ∧ b.stacks p.scratch = [] := by
  obtain ⟨nc, f, _, hf, _, hfs, hfi⟩ := spec words a hw hI hc hs
  have hbf : b = f := StructuredCalls.Eval.final_unique p.counter he hf
  subst f
  exact ⟨hfi, hfs⟩

/-- The invariant at every actual rank hit follows from the same BodySpec used
for the runtime theorem; no separate universal callback-correctness axiom is needed. -/
theorem Visits.hit_with_bodySpec {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape ranks : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body shape ranks n d e) (I : Data R S → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : BodySpec p body shape I budget) (hI : I d) (hs : d.stacks p.scratch = [])
    {rank : ℕ} (hr : rank ∈ ranks) :
    ∃ words a b nb, words.map List.length = shape ∧ CounterPrograms.value words.flatten = rank ∧
      a.stacks p.counter = Encoding.encodeList id words ∧ StructuredCalls.Eval body nb a b ∧
      (I a ∧ a.stacks p.scratch = []) ∧ (I b ∧ b.stacks p.scratch = []) := by
  apply h.hit_of_invariant (fun a => I a ∧ a.stacks p.scratch = []) ⟨hI, hs⟩ ?_ ?_ hr
  · intro words a b nb hw hc he ha
    exact spec.preserves words a b nb hw ha.1 hc ha.2 he
  · intro words a ha
    exact ⟨stable 0 a _ (advanceResult_outside p a words) ha.1,
      advanceResult_scratch p a words⟩

/-- Complete tuple coverage with the input/output invariants needed by the
concrete guard, lookup, and sunflower-checker proofs. -/
theorem Visits.covers_with_bodySpec {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {shape : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body shape (List.range' 0 (2 ^ shape.sum)) n d e)
    (I : Data R S → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : BodySpec p body shape I budget) (hI : I d) (hs : d.stacks p.scratch = [])
    (target : List (List Bool)) (ht : target.map List.length = shape) :
    ∃ a b nb, a.stacks p.counter = Encoding.encodeList id target ∧
      StructuredCalls.Eval body nb a b ∧
      (I a ∧ a.stacks p.scratch = []) ∧ (I b ∧ b.stacks p.scratch = []) := by
  apply h.covers_of_invariant (fun a => I a ∧ a.stacks p.scratch = []) ⟨hI, hs⟩ ?_ ?_ target ht
  · intro words a b nb hw hc he ha
    exact spec.preserves words a b nb hw ha.1 hc ha.2 he
  · intro words a ha
    exact ⟨stable 0 a _ (advanceResult_outside p a words) ha.1,
      advanceResult_scratch p a words⟩

end SubexponentialSAT.ExecCNFTupleEnumeration

end OAI.Algorithms
