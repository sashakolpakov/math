import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameBounds

namespace OAI.Algorithms

/-! Native control branches for source-polynomial lookup. Every literal and
conditional is executed; the universal-branch premise is an actual trace of
that fixed command and is supplied by the native table/emitter composition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def LiteralReady (a : Data) : Prop :=
  a.stacks 319=[] ∧ a.stacks 315=[] ∧ a.stacks 316=[] ∧ a.stacks 287=[]

def CompareReady (a : Data) : Prop :=
  a.stacks 301=[] ∧ a.stacks 302=[] ∧ a.stacks 303=[] ∧ a.stacks 307=[]

theorem cleared_eq_of_stacks {a b : Data} (h : b.stacks=a.stacks) :
    clearedStacks b=clearedStacks a :=
  congrArg (fun f : Fin 320 → List Bool => fun j => if j∈cleanupPorts then [] else f j) h

theorem covered_uncovered_cleanup (a : Data) (h : LiteralReady a)
    (h5 : a.regs 5=false) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ n ≤ 134*B+200, ∃ b : Data,
      Eval (.seq covered cleanup) n a b ∧
      b.stacks=Function.update (clearedStacks a) 287
        (SubexpKernelControl.pushWord (a.stacks 313)) := by
  obtain ⟨n,hn,b,he,hbs⟩ := literal_cleanup_eval 313 (Or.inl rfl) a h.1 h.2.1 h.2.2.1 h.2.2.2 B hB
  cases he with
  | seq hl hc =>
    refine ⟨_,?_,b,(Eval.ite_false (yes:=.seq compareBlocks (.ite 7 universal zero)) h5 hl).seq hc,hbs⟩
    have hh := hB 313
    omega

theorem uncovered_cleanup (a : Data) (h : LiteralReady a) (hr : CompareReady a)
    (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ n ≤ 161*B+232, ∃ b : Data,
      Eval (.seq uncovered cleanup) n a b ∧
      b.stacks=Function.update (clearedStacks a) 287
        (SubexpKernelControl.pushWord (if a.stacks 304=a.stacks 305 then a.stacks 314 else a.stacks 313)) := by
  obtain ⟨nc,hnc,m,hcmp,hms,_,h7⟩ := compareIndices_eval a hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hm : LiteralReady m := by simpa only [LiteralReady,hms] using h
  have hmB : ∀ j,(m.stacks j).length ≤ B := by simpa only [hms] using hB
  have hcB : nc ≤ 27*B+32 := by have h304:=hB 304; have h305:=hB 305; omega
  by_cases heq : a.stacks 304=a.stacks 305
  · obtain ⟨n,hn,b,he,hbs⟩ := literal_cleanup_eval 314 (Or.inr rfl) m hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 B hmB
    cases he with
    | seq hl hc =>
      have hh := (hcmp.seq (Eval.ite_true (no:=zero) (show m.regs 7=true by simp [h7,heq]) hl)).seq hc
      refine ⟨_,?_,b,hh,?_⟩
      · have h314:=hmB 314; omega
      · simpa only [hms,cleared_eq_of_stacks hms,ite_eq_left heq] using hbs
  · obtain ⟨n,hn,b,he,hbs⟩ := literal_cleanup_eval 313 (Or.inl rfl) m hm.1 hm.2.1 hm.2.2.1 hm.2.2.2 B hmB
    cases he with
    | seq hl hc =>
      have hh := (hcmp.seq (Eval.ite_false (yes:=one) (show m.regs 7=false by simp [h7,heq]) hl)).seq hc
      refine ⟨_,?_,b,hh,?_⟩
      · have h313:=hmB 313; omega
      · simpa only [hms,cleared_eq_of_stacks hms,ite_eq_right heq] using hbs

/-- Insert the two already-tested covered cases around the concrete native
universal source trace, without changing its output store. -/
theorem covered_attach {a b z : Data} {nc nu : ℕ}
    (hc : Eval compareBlocks nc a b) (h5 : a.regs 5=true) (h7 : b.regs 7=true)
    (hu : Eval (.seq universal cleanup) nu b z) :
    Eval (.seq covered cleanup) (nc+nu+2) a z := by
  cases hu with
  | seq hu hclean =>
    have he := (Eval.ite_true (no:=zero) h5
      (hc.seq (Eval.ite_true (no:=zero) h7 hu))).seq hclean
    change Eval (.seq covered cleanup) _ a z at he
    convert he using 1 ; omega

theorem selected_attach {a z : Data} {n : ℕ} {coveredFlag : Bool}
    (hf : a.regs 4=coveredFlag)
    (he : Eval (.seq (if coveredFlag then covered else uncovered) cleanup) n a z) :
    Eval (.seq (.ite 4 covered uncovered) cleanup) (n+1) a z := by
  cases coveredFlag
  · simp only [Bool.false_eq_true,ite_false] at he
    cases he with
    | seq h hclean =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        (Eval.ite_false (yes:=covered) hf h).seq hclean
  · simp only [ite_true] at he
    cases he with
    | seq h hclean =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        (Eval.ite_true (no:=uncovered) hf h).seq hclean

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
