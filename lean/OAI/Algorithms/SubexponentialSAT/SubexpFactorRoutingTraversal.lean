import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRoutingCallback

namespace OAI.Algorithms

/-! The record loop advances the aligned assignment stream physically.
No function of an untagged packet is assumed to determine its color. -/

namespace SubexponentialSAT.SubexpFactorRoutingTraversal

open BitProgram StructuredCalls SubexpFactorRoutingControl SubexpFactorRoutingCalls
open SubexpFactorRoutingCallback

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Item (r Q : ℕ) := MulticolorTypes.Word r Q × List Bool

def words {r Q : ℕ} (items : List (Item r Q)) : List Bool :=
  (items.map (fun x => Subexp.ReadPlan.encodeWord x.1)).flatten

def retained {r Q : ℕ} (t : Fin Q) (g : Fin r) (items : List (Item r Q)) : List (List Bool) :=
  (items.filter (fun x => decide (x.1 t = g))).map Prod.snd

def accumulate {r Q : ℕ} (t : Fin Q) (g : Fin r) : List (Item r Q) → List Bool → List Bool
  | [], acc => acc
  | x :: xs, acc => accumulate t g xs
      (if x.1 t = g then Subexp.TupleProgram.prependRecord x.2 acc else acc)

theorem accumulate_encoded {r Q : ℕ} (t : Fin Q) (g : Fin r)
    (items : List (Item r Q)) (acc : List (List Bool)) :
    accumulate t g items (Encoding.encodeList id acc) =
      Encoding.encodeList id ((retained t g items).reverse ++ acc) := by
  induction items generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      by_cases h : x.1 t = g
      · simpa [accumulate, retained, h, Subexp.TupleProgram.prependRecord,
          Encoding.encodeList, List.reverse_cons, List.append_assoc] using ih (x.2 :: acc)
      · simpa [accumulate, retained, h] using ih acc

def budget {r Q : ℕ} (W t r' g : ℕ) : List (Item r Q) → ℕ
  | [] => 1
  | x :: xs => 6 * x.2.length + callbackBudget W t r' g x.2.length + 7 + budget W t r' g xs

def Frame (a b : Data) : Prop :=
  ∀ i : Fin 48, i ≠ 7 → i ≠ 8 → i ≠ 9 → i ≠ 23 → b.stacks i = a.stacks i

theorem Frame.trans {a b c : Data} (hab : Frame a b) (hbc : Frame b c) : Frame a c := by
  intro i h7 h8 h9 h23
  exact (hbc i h7 h8 h9 h23).trans (hab i h7 h8 h9 h23)

theorem workClean_frame {a b : Data} (ha : WorkClean a) (hf : Frame a b) : WorkClean b := by
  intro i hi
  simp only [workPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [hf _ (by decide) (by decide) (by decide) (by decide)]
  all_goals exact ha _ (by simp [workPorts])

theorem parser_frame (d : Data) (v pr f : Bool) (source payload : List Bool) :
    Frame d (RecordPrograms.state parserPorts d v pr f source payload) := by
  intro i h7 h8 h9 h23
  simp [RecordPrograms.state, parserPorts, h8, h9]

/-- This induction follows the actual parser loop and its matching word
consumption, including when different factors have equal packet bytes. -/
theorem loop_eval {r Q : ℕ} (t : Fin Q) (g : Fin r)
    (items : List (Item r Q)) (suffix : List Bool) (d : Data)
    (hc : WorkClean d) (h4 : d.stacks 4 = unary r)
    (h5 : (d.stacks 5).length = Q * r)
    (h12 : d.stacks 12 = unary g.val) (h13 : d.stacks 13 = unary t.val)
    (h7 : d.stacks 7 = words items ++ suffix) :
    ∃ n ≤ budget (Q * r) t.val r g.val items, ∃ e : Data,
      Eval (RecordPrograms.loop parserPorts callback) n
        (RecordPrograms.afterTag parserPorts d (items.map Prod.snd) []) e ∧
      e.stacks 7 = suffix ∧ e.stacks 8 = [] ∧ e.stacks 9 = [] ∧
      e.stacks 23 = accumulate t g items (d.stacks 23) ∧ Frame d e := by
  induction items generalizing d with
  | nil =>
      let e := RecordPrograms.state parserPorts d false true false [] []
      refine ⟨1, le_rfl, e, .while_false (by simp [RecordPrograms.afterTag]),
        ?_, ?_, ?_, ?_, parser_frame d false true false [] []⟩
      · simpa [e, RecordPrograms.state, parserPorts, words] using h7
      · simp [e, RecordPrograms.state, parserPorts]
      · simp [e, RecordPrograms.state, parserPorts]
      · simp [e, RecordPrograms.state, parserPorts, accumulate]
  | cons x xs ih =>
      let tail := Encoding.encodeList id (xs.map Prod.snd)
      let a := RecordPrograms.state parserPorts d false true false tail x.2.reverse
      have hfa : Frame d a := parser_frame d false true false tail x.2.reverse
      have ha : WorkClean a := workClean_frame hc hfa
      have ha7 : a.stacks 7 = Subexp.ReadPlan.encodeWord x.1 ++ (words xs ++ suffix) := by
        simpa [a, RecordPrograms.state, parserPorts, words, List.flatten_cons,
          List.append_assoc] using h7
      obtain ⟨nc, hnc, regs, hregs, hcall⟩ := callback_eval x.1 t g x.2 (words xs ++ suffix) a ha
        ha7 (by simp [a, RecordPrograms.state, parserPorts])
        ((hfa 4 (by decide) (by decide) (by decide) (by decide)).trans h4)
        (by rw [hfa 5 (by decide) (by decide) (by decide) (by decide)]; exact h5)
        ((hfa 12 (by decide) (by decide) (by decide) (by decide)).trans h12)
        ((hfa 13 (by decide) (by decide) (by decide) (by decide)).trans h13)
      let b : Data :=
        ⟨regs, Function.update (Function.update (Function.update a.stacks 7 (words xs ++ suffix)) 9 []) 23
          (if x.1 t = g then Subexp.TupleProgram.prependRecord x.2 (a.stacks 23) else a.stacks 23)⟩
      have hfb : Frame a b := by
        intro i hi7 hi8 hi9 hi23
        simp [b, hi7, hi9, hi23]
      have hfdb : Frame d b := hfa.trans hfb
      have hb : WorkClean b := workClean_frame hc hfdb
      have hb7 : b.stacks 7 = words xs ++ suffix := by simp [b]
      have hb23 : b.stacks 23 =
          if x.1 t = g then Subexp.TupleProgram.prependRecord x.2 (d.stacks 23) else d.stacks 23 := by
        simp [b, a, RecordPrograms.state, parserPorts]
      have hbself : RecordPrograms.state parserPorts b false true false tail [] = b := by
        apply RecordPrograms.state_eq_self
        · exact (hregs 13 (by decide)).trans (RecordPrograms.state_tag parserPorts d _ _ _ _ _)
        · exact (hregs 14 (by decide)).trans (RecordPrograms.state_present parserPorts d _ _ _ _ _)
        · exact (hregs 15 (by decide)).trans (RecordPrograms.state_found parserPorts d _ _ _ _ _)
        · simp [b, a, RecordPrograms.state, parserPorts]
        · simp [b, parserPorts]
      have hreader : Eval (RecordPrograms.reader parserPorts) (6 * x.2.length + 4)
          (RecordPrograms.afterTag parserPorts d ((x :: xs).map Prod.snd) []) a := by
        simpa [RecordPrograms.afterTag, a, tail] using
          RecordPrograms.reader_eval parserPorts d x.2 tail [] true true false
      have hpop := RecordPrograms.pop_list_eval parserPorts b (xs.map Prod.snd) [] false true
      have hpstart : RecordPrograms.state parserPorts b false true false
          (Encoding.encodeList id (xs.map Prod.snd) ++ []) [] = b := by
        simpa [tail] using hbself
      rw [hpstart] at hpop
      have hbranch : Eval
          (.ite parserPorts.found (RecordPrograms.atom (.set parserPorts.tag false))
            (RecordPrograms.atom (.pop parserPorts.source parserPorts.tag parserPorts.present))) 2
          b (RecordPrograms.afterTag parserPorts b (xs.map Prod.snd) []) := by
        apply Eval.ite_false
        · exact (hregs 15 (by decide)).trans (RecordPrograms.state_found parserPorts d _ _ _ _ _)
        · exact hpop
      obtain ⟨nr, hnr, out, hrest, ho7, ho8, ho9, ho23, hfo⟩ := ih b hb
        ((hfdb 4 (by decide) (by decide) (by decide) (by decide)).trans h4)
        (by rw [hfdb 5 (by decide) (by decide) (by decide) (by decide)]; exact h5)
        ((hfdb 12 (by decide) (by decide) (by decide) (by decide)).trans h12)
        ((hfdb 13 (by decide) (by decide) (by decide) (by decide)).trans h13) hb7
      have hbody := hreader.seq (hcall.seq hbranch)
      have hrun := Eval.while_true
        (show (RecordPrograms.afterTag parserPorts d ((x :: xs).map Prod.snd) []).regs parserPorts.tag = true by
          simp [RecordPrograms.afterTag]) hbody hrest
      refine ⟨(6 * x.2.length + 4 + (nc + 2)) + nr + 1, ?_, out, ?_,
        ho7, ho8, ho9, ?_, hfdb.trans hfo⟩
      · have ha5 : (a.stacks 5).length = Q * r := by
          rw [hfa 5 (by decide) (by decide) (by decide) (by decide)]
          exact h5
        rw [ha5] at hnc
        simp only [budget]
        omega
      · simpa only [RecordPrograms.loop, RecordPrograms.body] using hrun
      · simpa only [accumulate, hb23] using ho23

theorem iterate_eval {r Q : ℕ} (t : Fin Q) (g : Fin r)
    (items : List (Item r Q)) (suffix : List Bool) (d : Data)
    (hc : WorkClean d) (h4 : d.stacks 4 = unary r)
    (h5 : (d.stacks 5).length = Q * r)
    (h12 : d.stacks 12 = unary g.val) (h13 : d.stacks 13 = unary t.val)
    (h7 : d.stacks 7 = words items ++ suffix)
    (h8 : d.stacks 8 = Encoding.encodeList id (items.map Prod.snd)) (h9 : d.stacks 9 = []) :
    ∃ n ≤ 2 + budget (Q * r) t.val r g.val items, ∃ e : Data,
      Eval (RecordPrograms.iterate parserPorts callback) n d e ∧
      e.stacks 7 = suffix ∧ e.stacks 8 = [] ∧ e.stacks 9 = [] ∧
      e.stacks 23 = accumulate t g items (d.stacks 23) ∧ Frame d e := by
  obtain ⟨n, hn, e, he, h7e, h8e, h9e, h23e, hframe⟩ :=
    loop_eval t g items suffix d hc h4 h5 h12 h13 h7
  have hstart : RecordPrograms.state parserPorts d (d.regs 13) (d.regs 14) (d.regs 15)
      (Encoding.encodeList id (items.map Prod.snd) ++ []) [] = d := by
    apply RecordPrograms.state_eq_self <;> try rfl
    · simpa [parserPorts] using h8
    · exact h9
  have hset := RecordPrograms.set_found_eval parserPorts d (d.regs 13) (d.regs 14)
    (d.regs 15) false (Encoding.encodeList id (items.map Prod.snd) ++ []) []
  rw [hstart] at hset
  have hpop := RecordPrograms.pop_list_eval parserPorts d (items.map Prod.snd) []
    (d.regs 13) (d.regs 14)
  exact ⟨1 + (1 + n), by omega, e, hset.seq (hpop.seq he),
    h7e, h8e, h9e, h23e, hframe⟩

end SubexponentialSAT.SubexpFactorRoutingTraversal

end OAI.Algorithms
