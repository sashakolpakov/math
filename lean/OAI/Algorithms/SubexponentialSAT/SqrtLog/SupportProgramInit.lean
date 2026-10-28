import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramLoop

namespace OAI.Algorithms

/-! Initialize the two constant tables with real bit writes. Only the unary
length counter and unary support budget are supplied as input data. -/
namespace SubexponentialSAT.SqrtLog.SupportProgram.Init

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram Steps

/-- Used only with literal, fixed-size words in the final initializer. -/
def writeBits (dst : Fin 10) : List Bool → Cmd 10 10
  | [] => .base .skip
  | b :: bs => .seq (writeBits dst bs) (pushConst dst 6 b)

theorem writeBits_eval (dst : Fin 10) (bits : List Bool) (a : Data) :
    ∃ b : Data, Eval (writeBits dst bits) (2 * bits.length) a b ∧
      b.stacks dst = bits ++ a.stacks dst ∧
      ∀ i, i ≠ dst → b.stacks i = a.stacks i := by
  induction bits generalizing a with
  | nil => exact ⟨a,.base (.skip _),rfl,by simp⟩
  | cons x xs ih =>
      obtain ⟨b,hb,hs,hf⟩ := ih a
      refine ⟨pushedState dst 6 x b, ?_, ?_, ?_⟩
      · convert hb.seq (pushConst_eval dst 6 x b) using 1 ; simp [writeBits]
      · simp [ hs]
      · intro i hi; simp [ hi, hf i hi]

abbrev tables (rows : Steps.Records) : Cmd 10 10 :=
  .seq (writeBits 0 (SubexponentialSAT.ProgramEncoding.encodeRecords rows))
    (.seq (writeBits 1 (SubexponentialSAT.ProgramEncoding.encodeRecords alphabet)) (writeBits 5 [false]))

theorem tables_eval (rows : Steps.Records) (a : Data) (h0 : a.stacks 0 = [])
    (h1 : a.stacks 1 = []) (h5 : a.stacks 5 = []) :
    ∃ b : Data, Eval (tables rows)
      (2 * (SubexponentialSAT.ProgramEncoding.encodeRecords rows).length + 20) a b ∧
      b.stacks 0 = SubexponentialSAT.ProgramEncoding.encodeRecords rows ∧
      b.stacks 1 = SubexponentialSAT.ProgramEncoding.encodeRecords alphabet ∧ b.stacks 5 = [false] ∧
      ∀ i, i ≠ 0 → i ≠ 1 → i ≠ 5 → b.stacks i = a.stacks i := by
  obtain ⟨b,hb,hb0,hbf⟩ := writeBits_eval 0 (SubexponentialSAT.ProgramEncoding.encodeRecords rows) a
  obtain ⟨c,hc,hc1,hcf⟩ := writeBits_eval 1 (SubexponentialSAT.ProgramEncoding.encodeRecords alphabet) b
  obtain ⟨d,hd,hd5,hdf⟩ := writeBits_eval 5 [false] c
  refine ⟨d, ?_, ?_, ?_, ?_, ?_⟩
  · convert hb.seq (hc.seq hd) using 1 ;
      norm_num [tables, alphabet, SubexponentialSAT.ProgramEncoding.encodeRecords, SubexponentialSAT.Encoding.encodeList,
        SubexponentialSAT.Encoding.frame]
  · rw [hdf 0 (by decide), hcf 0 (by decide), hb0, h0, List.append_nil]
  · rw [hdf 1 (by decide), hc1, hbf 1 (by decide), h1, List.append_nil]
  · rw [hd5, hcf 5 (by decide), hbf 5 (by decide), h5, List.append_nil]
  · intro i hi0 hi1 hi5
    exact (hdf i hi5).trans ((hcf i hi1).trans (hbf i hi0))

abbrev peek : Cmd 10 10 := .base (.atom (.peek 9 6 7))
def peeked (a : Data) : Data := ⟨readRegs a.regs 6 7 (a.stacks 9).head?, a.stacks⟩
theorem peek_eval (a : Data) : Eval peek 1 a (peeked a) := .base (.atom _ _)

abbrev command : Cmd 10 10 := .seq peek (.ite 7 (tables [[]]) (tables []))

def Empty (budget : List Bool) (a : Data) : Prop :=
  (∀ i, i ≠ 8 → i ≠ 9 → a.stacks i = []) ∧ a.stacks 9 = budget

theorem command_eval (budget : List Bool) (a : Data) (h : Empty budget a) :
    ∃ m ≤ 28, ∃ b : Data, Eval command m a b ∧ Loop.Invariant budget 0 b ∧
      b.stacks 8 = a.stacks 8 := by
  let c := peeked a
  have hempty (i : Fin 10) (hi8 : i ≠ 8) (hi9 : i ≠ 9) : c.stacks i = [] := h.1 i hi8 hi9
  cases budget with
  | nil =>
      obtain ⟨b,hb,h0,h1,h5,hf⟩ := tables_eval [] c
        (hempty 0 (by decide) (by decide)) (hempty 1 (by decide) (by decide))
        (hempty 5 (by decide) (by decide))
      have hguard : c.regs 7 = false := by simp [c, peeked, readRegs, h.2]
      refine ⟨24, by decide, b, ?_, ?_, ?_⟩
      · exact (peek_eval a).seq (.ite_false hguard hb)
      · refine ⟨[], ?_, h0,h1, ?_, ?_, ?_, h5, ?_, ?_, ?_⟩
        · constructor <;> simp []
        · rw [hf 2 (by decide) (by decide) (by decide)]; exact hempty 2 (by decide) (by decide)
        · rw [hf 3 (by decide) (by decide) (by decide)]; exact hempty 3 (by decide) (by decide)
        · rw [hf 4 (by decide) (by decide) (by decide)]; exact hempty 4 (by decide) (by decide)
        · rw [hf 6 (by decide) (by decide) (by decide)]; exact hempty 6 (by decide) (by decide)
        · rw [hf 7 (by decide) (by decide) (by decide)]; exact hempty 7 (by decide) (by decide)
        · exact (hf 9 (by decide) (by decide) (by decide)).trans h.2
      · exact hf 8 (by decide) (by decide) (by decide)
  | cons bit budget =>
      obtain ⟨b,hb,h0,h1,h5,hf⟩ := tables_eval [[]] c
        (hempty 0 (by decide) (by decide)) (hempty 1 (by decide) (by decide))
        (hempty 5 (by decide) (by decide))
      have hguard : c.regs 7 = true := by simp [c, peeked, readRegs, h.2]
      refine ⟨28, by decide, b, ?_, ?_, ?_⟩
      · exact (peek_eval a).seq (.ite_true hguard hb)
      · refine ⟨[[]], ?_, h0,h1, ?_, ?_, ?_, h5, ?_, ?_, ?_⟩
        · refine ⟨by simp, ?_⟩
          intro xs; cases xs <;> simp
        · rw [hf 2 (by decide) (by decide) (by decide)]; exact hempty 2 (by decide) (by decide)
        · rw [hf 3 (by decide) (by decide) (by decide)]; exact hempty 3 (by decide) (by decide)
        · rw [hf 4 (by decide) (by decide) (by decide)]; exact hempty 4 (by decide) (by decide)
        · rw [hf 6 (by decide) (by decide) (by decide)]; exact hempty 6 (by decide) (by decide)
        · rw [hf 7 (by decide) (by decide) (by decide)]; exact hempty 7 (by decide) (by decide)
        · exact (hf 9 (by decide) (by decide) (by decide)).trans h.2
      · exact hf 8 (by decide) (by decide) (by decide)

end SubexponentialSAT.SqrtLog.SupportProgram.Init

end OAI.Algorithms
