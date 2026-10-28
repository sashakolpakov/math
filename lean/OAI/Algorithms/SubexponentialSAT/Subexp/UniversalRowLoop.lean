import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowTermProgram

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)
open UniversalRowFactorLoop (indexWord)

structure Tables where
  values : List Word
  inverses : List Word
  negatives : List Word
  differences : List (List Word)

def Tables.rows (t : Tables) : List Word := t.differences.map List.flatten

theorem rows_getD (t : Tables) (i : ℕ) :
    t.rows.getD i [] = (t.differences.getD i []).flatten := by
  rcases t with ⟨values, inverses, negatives, differences⟩
  induction differences generalizing i with
  | nil => simp [Tables.rows]
  | cons d ds ih =>
      cases i <;> simp_all [Tables.rows]

structure Valid (t : Tables) (width rowWidth : Word) (positions : List ℕ) : Prop where
  values : ∀ row ∈ t.values, row.length = width.length
  inverses : ∀ row ∈ t.inverses, row.length = width.length
  negatives : ∀ row ∈ t.negatives, row.length = width.length
  rows : ∀ row ∈ t.rows, row.length = rowWidth.length
  bounds : ∀ i ∈ positions,
    i < t.values.length ∧ i < t.inverses.length ∧ i < t.differences.length
  differences : ∀ i ∈ positions, ∀ row ∈ t.differences.getD i [], row.length = width.length
  innerBounds : ∀ i ∈ positions, ∀ j ∈ positions,
    j < (t.differences.getD i []).length ∧ j < t.negatives.length

def ready (t : Tables) (width rowWidth : Word) (positions : List ℕ) (a : Data) : Prop :=
  UniversalRowTermProgram.Ready t.values t.inverses t.negatives t.rows width rowWidth positions 0 a

def ports : RecordPrograms.Ports 8 32 where
  tag := 5
  present := 6
  found := 7
  source := 17
  payload := 16
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def term (t : Tables) (positions : List ℕ) (i : ℕ) : UniversalRowProgram.Term Word :=
  UniversalRowTermProgram.term t.values t.inverses t.negatives (t.differences.getD i []) positions i

def prepend (t : Tables) (positions : List ℕ) (i : ℕ) (acc : Word) : Word :=
  true :: (Encoding.frame (UniversalRowProgram.encodeTerm (term t positions i)) ++ acc)

def cost (t : Tables) (width rowWidth : Word) (positions : List ℕ) (bits : Word) : ℕ :=
  UniversalRowTermProgram.cost t.values t.inverses t.negatives (t.differences.getD bits.length [])
    width rowWidth positions bits.length

def invariant (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (frame : Fin 32 → Word) (a : Data) : Prop :=
  ready t width rowWidth positions a ∧ ∀ j, j ≠ 31 → a.stacks j = frame j

def effect (t : Tables) (positions : List ℕ) (bits : Word) (a b : Data) : Prop :=
  b.stacks 31 = prepend t positions bits.length (a.stacks 31)

theorem callback_contract (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (frame : Fin 32 → Word) :
    RecordPrograms.CallbackContractWithOn ports UniversalRowTermProgram.command (fun _ => false)
      (cost t width rowWidth positions) (invariant t width rowWidth positions frame)
      (effect t positions) (fun bits => ∃ i ∈ positions, bits = indexWord i) := by
  intro bits tail base hvalid hbase
  obtain ⟨i, hi, rfl⟩ := hvalid
  let a := RecordPrograms.state ports base false true false tail (indexWord i).reverse
  have ha : UniversalRowTermProgram.Ready t.values t.inverses t.negatives t.rows
      width rowWidth positions i a := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [a, RecordPrograms.state, ports] using hbase.1.values
    · simpa [a, RecordPrograms.state, ports] using hbase.1.inverses
    · simpa [a, RecordPrograms.state, ports] using hbase.1.negatives
    · simpa [a, RecordPrograms.state, ports] using hbase.1.rows
    · simpa [a, RecordPrograms.state, ports] using hbase.1.indices
    · simpa [a, RecordPrograms.state, ports] using hbase.1.width
    · simpa [a, RecordPrograms.state, ports] using hbase.1.rowWidth
    · simp [a, RecordPrograms.state, ports]
    · intro j hj
      have he := hbase.1.empty j hj
      fin_cases j <;> simp_all [a, RecordPrograms.state, ports]
  obtain ⟨n, hn, b, hb, h5, h6, h7, hbs⟩ := UniversalRowTermProgram.command_eval
    t.values t.inverses t.negatives t.rows (t.differences.getD i []) width rowWidth positions i a ha
    (valid.bounds i hi).1 (valid.bounds i hi).2.1
    (by simpa [Tables.rows] using (valid.bounds i hi).2.2)
    valid.values valid.inverses valid.rows (valid.differences i hi) valid.negatives
    (rows_getD t i) (valid.innerBounds i hi)
  let next : Data := ⟨b.regs, Function.update base.stacks 31 (b.stacks 31)⟩
  have hnext : invariant t width rowWidth positions frame next := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [next] using hbase.1.values
    · simpa [next] using hbase.1.inverses
    · simpa [next] using hbase.1.negatives
    · simpa [next] using hbase.1.rows
    · simpa [next] using hbase.1.indices
    · simpa [next] using hbase.1.width
    · simpa [next] using hbase.1.rowWidth
    · simpa [next] using hbase.1.index
    · intro j hj
      have he := hbase.1.empty j hj
      fin_cases j <;> simp_all [next]
    · intro j hj
      simpa [next, hj] using hbase.2 j hj
  have hend : b = RecordPrograms.state ports next false true false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp_all [ next, ports]
    · funext j
      rw [hbs]
      by_cases hj16 : j = 16 <;> by_cases hj17 : j = 17 <;> by_cases hj31 : j = 31 <;>
        simp_all [RecordPrograms.state, next, a, ports, Function.update_apply]
  refine ⟨n, next, ?_, hnext, ?_, ?_⟩
  · simpa [cost] using hn
  · simp [effect, next, hbs, a, RecordPrograms.state, ports, prepend, term]
  · rw [← hend]
    exact hb

abbrev loop : Cmd 8 32 := RecordPrograms.iterate ports UniversalRowTermProgram.command

def output (t : Tables) (positions : List ℕ) (records : List Word) (acc : Word) : Word :=
  records.foldl (fun out bits => prepend t positions bits.length out) acc

theorem output_append (t : Tables) (positions : List ℕ) (xs ys : List Word) (acc : Word) :
    output t positions (xs ++ ys) acc = output t positions ys (output t positions xs acc) := by
  simp [output, List.foldl_append]

theorem output_reverse (t : Tables) (positions traversal : List ℕ)
    (tail : List (UniversalRowProgram.Term Word)) :
    output t positions (traversal.reverse.map indexWord)
        (Encoding.encodeList UniversalRowProgram.encodeTerm tail) =
      Encoding.encodeList UniversalRowProgram.encodeTerm (traversal.map (term t positions) ++ tail) := by
  induction traversal with
  | nil => simp [output]
  | cons i rest ih =>
      rw [List.reverse_cons, List.map_append, output_append]
      change prepend t positions (indexWord i).length
        (output t positions (rest.reverse.map indexWord)
          (Encoding.encodeList UniversalRowProgram.encodeTerm tail)) = _
      rw [ih]
      simp [prepend, Encoding.encodeList]

theorem loop_eval (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (base : Data)
    (hbase : ready t width rowWidth positions base) (hacc : base.stacks 31 = [false])
    (v pr f : Bool) :
    ∃ n ≤ 3 + RecordPrograms.budget (cost t width rowWidth positions) (positions.reverse.map indexWord),
      ∃ next : Data,
        Eval loop n
          (RecordPrograms.state ports base v pr f
            (UniversalRowTermProgram.indices positions) [])
          (RecordPrograms.state ports next false true false [] []) ∧
        ready t width rowWidth positions next ∧
        next.stacks 31 = Encoding.encodeList UniversalRowProgram.encodeTerm
          (positions.map (term t positions)) ∧
        (∀ j, j ≠ 31 → next.stacks j = base.stacks j) := by
  have hv : ∀ bits ∈ positions.reverse.map indexWord, ∃ i ∈ positions, bits = indexWord i := by
    intro bits hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨i, by simpa using hi, rfl⟩
  obtain ⟨n, next, hn, hnext, history, he⟩ := RecordPrograms.iterate_run_with_on ports
    UniversalRowTermProgram.command (fun _ => false) (cost t width rowWidth positions)
    (invariant t width rowWidth positions base.stacks) (effect t positions)
    (fun bits => ∃ i ∈ positions, bits = indexWord i)
    (callback_contract t width rowWidth positions valid base.stacks)
    (positions.reverse.map indexWord) [] base hv ⟨hbase, by intros; rfl⟩ v pr f
  refine ⟨n, hn, next, ?_, hnext.1, ?_, hnext.2⟩
  · simpa [loop, UniversalRowTermProgram.indices, UniversalRowFactorLoop.unread_false,
      UniversalRowFactorLoop.any_false] using he
  · have ho := history.fold_of_false (by intros; rfl) (fun a => a.stacks 31)
      (fun out bits => prepend t positions bits.length out) (by intros; assumption)
    change next.stacks 31 = output t positions (positions.reverse.map indexWord) (base.stacks 31) at ho
    rw [ho, hacc]
    simpa only [Encoding.encodeList, List.append_nil] using output_reverse t positions positions []

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
