import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntry

namespace OAI.Algorithms

/-!
# Actual traversal of one dense global-matrix row

The fixed iterator parses every generated column descriptor and invokes the
concrete entry program.  Its output is the reversed row prefixed to an
arbitrary accumulator, so successive rows can be emitted without copying
previous output.  A final transfer restores the complete matrix order.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisRows

open BitProgram StructuredCalls
open GlobalBasisColumns (Descriptor)
open GlobalBasisEntry (Row Ready Valid entryFrame)

abbrev Data := GlobalBasisEntry.Data
abbrev Code := GlobalBasisEntry.Code

def ports : RecordPrograms.Ports 16 32 where
  tag := 13
  present := 14
  found := 15
  source := 6
  payload := 7
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def records (xs : List Descriptor) := xs.map Descriptor.encode
def rowBits {p : ℕ} (R : Row p) (xs : List Descriptor) := xs.flatMap (entryFrame R)
def command : Code := RecordPrograms.iterate ports GlobalBasisEntry.command

def Invariant {p : ℕ} [Fact p.Prime] (R : Row p) (d : Data) : Prop :=
  Ready R d ∧ d.stacks 8 = [] ∧ d.stacks 9 = [] ∧ d.stacks 10 = []

theorem invariant_state {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data}
    (h : Invariant R d) (v pr f : Bool) (source payload : List Bool) :
    Invariant R (RecordPrograms.state ports d v pr f source payload) := by
  rcases h with ⟨h, h8, h9, h10⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · simpa [RecordPrograms.state, ports] using h.table
    · simpa [RecordPrograms.state, ports] using h.dimension
    · simpa [RecordPrograms.state, ports] using h.coordinate
    · simpa [RecordPrograms.state, ports] using h.block
    · simpa [RecordPrograms.state, ports] using h.color
    · simpa [RecordPrograms.state, ports] using h.rank
    · simpa [RecordPrograms.state, ports] using h.width
    · simpa [RecordPrograms.state, ports] using h.zero
    · simpa [RecordPrograms.state, ports] using h.one
    · simpa [RecordPrograms.state, ports] using h.kind
    · simpa [RecordPrograms.state, ports] using h.output
    · intro i hi
      have hi6 : i ≠ 6 := by intro he; subst i; change 16 ≤ 6 at hi; omega
      have hi7 : i ≠ 7 := by intro he; subst i; change 16 ≤ 7 at hi; omega
      simpa [RecordPrograms.state, ports, hi6, hi7] using h.work i hi
  · simpa [RecordPrograms.state, ports] using h8
  · simpa [RecordPrograms.state, ports] using h9
  · simpa [RecordPrograms.state, ports] using h10

theorem invariant_output {p : ℕ} [Fact p.Prime] {R : Row p} {d e : Data}
    (h : Invariant R d) (frame : List Bool)
    (hs : e.stacks = GlobalBasisEntry.output d.stacks frame)
    (hr : e.regs 6 = d.regs 6) : Invariant R e := by
  rcases h with ⟨h, h8, h9, h10⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · simpa [hs, GlobalBasisEntry.output] using h.table
    · simpa [hs, GlobalBasisEntry.output] using h.dimension
    · simpa [hs, GlobalBasisEntry.output] using h.coordinate
    · simpa [hs, GlobalBasisEntry.output] using h.block
    · simpa [hs, GlobalBasisEntry.output] using h.color
    · simpa [hs, GlobalBasisEntry.output] using h.rank
    · simpa [hs, GlobalBasisEntry.output] using h.width
    · simpa [hs, GlobalBasisEntry.output] using h.zero
    · simpa [hs, GlobalBasisEntry.output] using h.one
    · exact hr.trans h.kind
    · simpa [hs, GlobalBasisEntry.output] using h.output
    · intro i hi
      have hi7 : i ≠ 7 := by intro he; subst i; change 16 ≤ 7 at hi; omega
      have hi12 : i ≠ 12 := by intro he; subst i; change 16 ≤ 12 at hi; omega
      simpa [hs, GlobalBasisEntry.output, hi7, hi12] using h.work i hi
  · simpa [hs, GlobalBasisEntry.output] using h8
  · simpa [hs, GlobalBasisEntry.output] using h9
  · simpa [hs, GlobalBasisEntry.output] using h10

def budget {p : ℕ} (R : Row p) : List Descriptor → ℕ
  | [] => 0
  | x :: xs => 6 * x.encode.length + GlobalBasisEntry.cost R x + 7 + budget R xs

theorem loop_run {p : ℕ} [Fact p.Prime] (R : Row p) (xs : List Descriptor)
    (suffix : List Bool) (base : Data) (hi : Invariant R base)
    (hv : ∀ x ∈ xs, Valid R x) :
    ∃ n e, n ≤ 1 + budget R xs ∧ Invariant R e ∧
      e.stacks 12 = (rowBits R xs).reverse ++ base.stacks 12 ∧
      Eval (RecordPrograms.loop ports GlobalBasisEntry.command) n
        (RecordPrograms.afterTag ports base (records xs) suffix)
        (RecordPrograms.state ports e false true false suffix []) := by
  induction xs generalizing base with
  | nil =>
    refine ⟨1, base, by simp [budget], hi, by simp [rowBits], ?_⟩
    exact .while_false (by simp [RecordPrograms.afterTag, records])
  | cons x xs ih =>
    let tail := Encoding.encodeList id (records xs) ++ suffix
    let a := RecordPrograms.state ports base false true false tail x.encode.reverse
    have hai : Invariant R a := invariant_state hi _ _ _ _ _
    obtain ⟨n, middle, hn, he, hs, hr, h13, h14, h15⟩ :=
      GlobalBasisEntry.command_eval hai.1 x (by simp [a, RecordPrograms.state, ports])
        hai.2.1 hai.2.2.1 hai.2.2.2 (hv x (by simp))
    have hmi : Invariant R middle := invariant_output hai _ hs hr
    have hm6 : middle.stacks 6 = tail := by
      simp [hs, GlobalBasisEntry.output, a, RecordPrograms.state, ports]
    have hm7 : middle.stacks 7 = [] := by simp [hs, GlobalBasisEntry.output]
    have hmid : RecordPrograms.state ports middle false true false tail [] = middle :=
      RecordPrograms.state_eq_self ports middle _ _ _ _ _ h13 h14 h15 hm6 hm7
    have hreader : Eval (RecordPrograms.reader ports) (6 * x.encode.length + 4)
        (RecordPrograms.afterTag ports base (records (x :: xs)) suffix) a := by
      simpa [RecordPrograms.afterTag, records, a, tail] using
        RecordPrograms.reader_eval ports base x.encode tail [] true true false
    have hbranch : Eval
        (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
          (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
        middle (RecordPrograms.afterTag ports middle (records xs) suffix) := by
      have hp := RecordPrograms.pop_list_eval ports middle (records xs) suffix false true
      change Eval _ 1 (RecordPrograms.state ports middle false true false tail []) _ at hp
      rw [hmid] at hp
      exact .ite_false h15 hp
    obtain ⟨m, next, hm, hni, hout, hloop⟩ := ih middle hmi
      (fun y hy => hv y (by simp [hy]))
    have hbody := hreader.seq (he.seq hbranch)
    have hall := Eval.while_true
      (show (RecordPrograms.afterTag ports base (records (x :: xs)) suffix).regs ports.tag = true by
        simp [RecordPrograms.afterTag, records]) hbody hloop
    refine ⟨(6 * x.encode.length + 4 + (n + 2)) + m + 1, next, ?_, hni, ?_, hall⟩
    · simp only [budget]
      omega
    · rw [hout]
      simp [hs, GlobalBasisEntry.output, a, RecordPrograms.state, ports, rowBits,
        List.reverse_append, List.append_assoc]

/-- The actual iterator consumes exactly the descriptor list. Its old source
suffix and reverse-output accumulator are preserved without being copied. -/
theorem command_eval {p : ℕ} [Fact p.Prime] (R : Row p) (xs : List Descriptor)
    (suffix : List Bool) (base : Data) (hi : Invariant R base)
    (hv : ∀ x ∈ xs, Valid R x) (v pr f : Bool) :
    ∃ n e, n ≤ 3 + budget R xs ∧ Invariant R e ∧
      e.stacks 6 = suffix ∧ e.stacks 7 = [] ∧
      e.stacks 12 = (rowBits R xs).reverse ++ base.stacks 12 ∧
      Eval command n
        (RecordPrograms.state ports base v pr f
          (Encoding.encodeList id (records xs) ++ suffix) []) e := by
  obtain ⟨n, next, hn, hni, hout, hloop⟩ := loop_run R xs suffix base hi hv
  let e := RecordPrograms.state ports next false true false suffix []
  refine ⟨1 + (1 + n), e, by omega, invariant_state hni _ _ _ _ _, ?_, ?_, ?_, ?_⟩
  · simp [e, RecordPrograms.state, ports]
  · simp [e, RecordPrograms.state, ports]
  · simpa [e, RecordPrograms.state, ports] using hout
  · exact (RecordPrograms.set_found_eval ports base v pr f false _ []).seq
      ((RecordPrograms.pop_list_eval ports base (records xs) suffix v pr).seq hloop)

def program := compiled command 6 12

theorem program_runsIn {p : ℕ} [Fact p.Prime] (R : Row p) (xs : List Descriptor)
    (suffix : List Bool) (base : Data) (hi : Invariant R base)
    (hv : ∀ x ∈ xs, Valid R x) (v pr f : Bool) :
    ∃ e : Data, Invariant R e ∧ e.stacks 6 = suffix ∧ e.stacks 7 = [] ∧
      e.stacks 12 = (rowBits R xs).reverse ++ base.stacks 12 ∧
      RunsIn program (4 + budget R xs)
        ((RecordPrograms.state ports base v pr f
          (Encoding.encodeList id (records xs) ++ suffix) []).withPC (some program.entry))
        (e.withPC none) := by
  obtain ⟨n, e, hn, hi, h6, h7, h12, he⟩ := command_eval R xs suffix base hi hv v pr f
  exact ⟨e, hi, h6, h7, h12, n + 1, by omega, compiled_halt_trace he 6 12⟩

theorem rowBits_length {p : ℕ} (R : Row p) (xs : List Descriptor) :
    (rowBits R xs).length = xs.length * GlobalBasisEntry.frameWidth p := by
  induction xs with
  | nil => simp [rowBits]
  | cons x xs ih =>
    simp [rowBits, entryFrame, Nat.add_mul, Nat.add_comm] at ih ⊢

def baseSize {p : ℕ} (R : Row p) : ℕ :=
  R.N + R.coordinate + R.block + R.color + R.rank + GlobalBasisEntry.frameWidth p + 1

def encodedSize (xs : List Descriptor) : ℕ :=
  (Encoding.encodeList id (records xs)).length

theorem descriptorSize_le (x : Descriptor) :
    GlobalBasisEntry.descriptorSize x ≤ x.encode.length := by
  cases x <;> simp [GlobalBasisEntry.descriptorSize, GlobalBasisEntry.firstIndex,
    GlobalBasisEntry.secondIndex, GlobalBasisEntry.thirdIndex, Descriptor.encode,
    GlobalBasisColumns.localPayload, GlobalBasisColumns.unary] <;> omega

theorem member_length_le {x : Descriptor} {xs : List Descriptor} (hx : x ∈ xs) :
    x.encode.length ≤ encodedSize xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [encodedSize, records, Encoding.encodeList]
      omega
    · have h := ih hx
      simp [encodedSize, records, Encoding.encodeList] at *
      omega

theorem length_le_encodedSize (xs : List Descriptor) : xs.length ≤ encodedSize xs := by
  induction xs with
  | nil => simp [encodedSize, records, Encoding.encodeList]
  | cons x xs ih =>
    simp [encodedSize, records, Encoding.encodeList] at *
    omega

theorem budget_le_uniform {p : ℕ} (R : Row p) (xs : List Descriptor) (B : ℕ)
    (hB : ∀ x ∈ xs, 6 * x.encode.length + GlobalBasisEntry.cost R x + 7 ≤ B) :
    budget R xs ≤ xs.length * B := by
  induction xs with
  | nil => simp [budget]
  | cons x xs ih =>
    have hx := hB x (by simp)
    have hs := ih (fun y hy => hB y (by simp [hy]))
    simp only [budget, List.length_cons]
    nlinarith

/-- A uniform quartic bound in serialized descriptor bytes and retained
unary row metadata. It does not charge the old matrix accumulator. -/
theorem budget_polynomial {p : ℕ} (R : Row p) (xs : List Descriptor) :
    4 + budget R xs ≤ 2000 * (baseSize R + encodedSize xs + 1)^4 := by
  let B := baseSize R + encodedSize xs + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hB2 : B ≤ B^2 := by nlinarith
  have hB3 : B^2 ≤ B^3 := by nlinarith [Nat.mul_le_mul_right B hB2]
  have hB4 : B^3 ≤ B^4 := by nlinarith [Nat.mul_le_mul_right B hB3]
  have hstep : ∀ x ∈ xs, 6 * x.encode.length + GlobalBasisEntry.cost R x + 7 ≤ 1013 * B^3 := by
    intro x hx
    have henc := member_length_le hx
    have hlen : x.encode.length ≤ B := henc.trans (by dsimp [B]; omega)
    have hlocal : GlobalBasisEntry.localSize R x ≤ B := by
      have hd := descriptorSize_le x
      simp only [GlobalBasisEntry.localSize] at *
      dsimp [B, baseSize]
      omega
    have hc := (GlobalBasisEntry.cost_le_cubic R x).trans
      (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hlocal 3))
    nlinarith
  have hs := budget_le_uniform R xs (1013 * B^3) hstep
  have hlen : xs.length ≤ B := (length_le_encodedSize xs).trans (by dsimp [B]; omega)
  have hm := Nat.mul_le_mul_right (1013 * B^3) hlen
  change 4 + budget R xs ≤ 2000 * B^4
  nlinarith

theorem program_runsIn_polynomial {p : ℕ} [Fact p.Prime] (R : Row p) (xs : List Descriptor)
    (suffix : List Bool) (base : Data) (hi : Invariant R base)
    (hv : ∀ x ∈ xs, Valid R x) (v pr f : Bool) :
    ∃ e : Data, Invariant R e ∧ e.stacks 6 = suffix ∧ e.stacks 7 = [] ∧
      e.stacks 12 = (rowBits R xs).reverse ++ base.stacks 12 ∧
      RunsIn program (2000 * (baseSize R + encodedSize xs + 1)^4)
        ((RecordPrograms.state ports base v pr f
          (Encoding.encodeList id (records xs) ++ suffix) []).withPC (some program.entry))
        (e.withPC none) := by
  obtain ⟨e, hi, h6, h7, h12, he⟩ := program_runsIn R xs suffix base hi hv v pr f
  exact ⟨e, hi, h6, h7, h12, he.mono (budget_polynomial R xs)⟩

end SubexponentialSAT.Subexp.GlobalBasisRows

end OAI.Algorithms
