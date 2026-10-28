import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-! The Boolean part of a local squarefree head weight, executed by a fixed
parallel scan of the assignment, support mask, and head mask. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram

open SubexponentialSAT BitProgram StructuredCalls

/-- Missing mask cells are unselected; the intended inputs have equal length. -/
def good : List Bool → List Bool → List Bool → Bool
  | [], _, _ => true
  | a :: as, ss, hs => (!(ss.headD false && hs.headD false) || a) &&
      good as ss.tail hs.tail

abbrev Data := StructuredProgram.State 8 3

abbrev tapes (a s h : List Bool) : Fin 3 → List Bool := ![a,s,h]
abbrev data (r : Fin 8 → Bool) (a s h : List Bool) : Data := ⟨r,tapes a s h⟩

def ready (r : Fin 8 → Bool) (a s h : List Bool) : Data :=
  data (readRegs r 0 3 a.head?) a.tail s h

abbrev popAssignment : StructuredProgram.Cmd 8 3 := .atom (.pop 0 0 3)
abbrev body : StructuredProgram.Cmd 8 3 :=
  .seq (.atom (.pop 1 1 4)) <|
  .seq (.atom (.pop 2 2 5)) <|
  .seq (.atom (.band 7 1 2)) <|
  .seq (.atom (.bnot 7 7)) <|
  .seq (.atom (.bor 7 7 0)) <|
  .seq (.atom (.band 6 6 7)) popAssignment

abbrev loop : StructuredProgram.Cmd 8 3 := .while 3 body
abbrev command : Cmd 8 3 := .base <|
  .seq (.atom (.set 6 true)) (.seq popAssignment loop)

private theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

private theorem popAssignment_eval (r : Fin 8 → Bool) (a s h : List Bool) :
    StructuredProgram.Eval popAssignment 1 (data r a s h) (ready r a s h) := by
  have he := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop 0 0 3) (data r a s h)
  convert he using 1
  apply state_ext
  · rfl
  · funext i; fin_cases i <;> rfl

private theorem body_eval (r : Fin 8 → Bool) (a s h : Bool) (as ss hs : List Bool) :
    ∃ rf, StructuredProgram.Eval body 7
      (ready r (a::as) (s::ss) (h::hs)) (ready rf as ss hs) ∧
      rf 6 = (r 6 && (!(s && h) || a)) := by
  let d0 := ready r (a::as) (s::ss) (h::hs)
  let d1 := (StructuredProgram.Atom.pop 1 1 4).eval d0
  let d2 := (StructuredProgram.Atom.pop 2 2 5).eval d1
  let d3 := (StructuredProgram.Atom.band 7 1 2).eval d2
  let d4 := (StructuredProgram.Atom.bnot 7 7).eval d3
  let d5 := (StructuredProgram.Atom.bor 7 7 0).eval d4
  let d6 := (StructuredProgram.Atom.band 6 6 7).eval d5
  have hd : d6 = data d6.regs as ss hs := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [d0,d1,d2,d3,d4,d5,d6,ready,data,tapes,
        StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,execInstr,
        StructuredProgram.State.ofCfg]
  have hp := popAssignment_eval d6.regs as ss hs
  rw [←hd] at hp
  refine ⟨d6.regs, ?_, ?_⟩
  · exact StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.pop 1 1 4) d0)
      (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.pop 2 2 5) d1)
        (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.band 7 1 2) d2)
          (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.bnot 7 7) d3)
            (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.bor 7 7 0) d4)
              (StructuredProgram.Eval.seq (StructuredProgram.Eval.atom (.band 6 6 7) d5) hp)))))
  · simp [d0,d1,d2,d3,d4,d5,d6,ready,data,tapes,readRegs,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,execInstr,
      StructuredProgram.State.ofCfg]

private theorem loop_eval (r : Fin 8 → Bool) (a s h : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, StructuredProgram.Eval loop (8*a.length+1) (ready r a s h) (data rf [] [] []) ∧
      rf 6 = (r 6 && good a s h) := by
  induction a generalizing r s h with
  | nil =>
    have hs : s=[] := List.length_eq_zero_iff.mp has.symm
    have hh : h=[] := List.length_eq_zero_iff.mp hah.symm
    subst s; subst h
    refine ⟨readRegs r 0 3 none, ?_, ?_⟩
    · exact StructuredProgram.Eval.while_false (by simp [ready,data,readRegs])
    · simp [readRegs,good]
  | cons a as ih =>
    cases s with
    | nil => simp at has
    | cons s ss =>
      cases h with
      | nil => simp at hah
      | cons h hs =>
        obtain ⟨rb,eb,hb⟩ := body_eval r a s h as ss hs
        obtain ⟨rf,ef,hf⟩ := ih rb ss hs (by simpa using has) (by simpa using hah)
        refine ⟨rf, ?_, ?_⟩
        · have he := StructuredProgram.Eval.while_true
            (by simp [ready,data,readRegs] : (ready r (a::as) (s::ss) (h::hs)).regs 3 = true)
            eb ef
          convert he using 1 ; simp [] ; omega
        · rw [hf,hb]
          simp [good,Bool.and_assoc]

/-- Exact scan execution. All three work tapes are consumed and register6 is
true precisely when every selected assignment bit is true. -/
theorem command_eval (r : Fin 8 → Bool) (a s h : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, Eval command (8*a.length+3) (data r a s h) (data rf [] [] []) ∧
      rf 6 = good a s h := by
  let r0 := Function.update r 6 true
  have e0 : StructuredProgram.Eval (.atom (.set 6 true)) 1
      (data r a s h) (data r0 a s h) := StructuredProgram.Eval.atom _ _
  have ep := popAssignment_eval r0 a s h
  obtain ⟨rf,ef,hf⟩ := loop_eval r0 a s h has hah
  refine ⟨rf, ?_, ?_⟩
  · convert Eval.base (e0.seq (ep.seq ef)) using 1 ; omega
  · simpa [r0] using hf

abbrev program := compiled command 0 0

theorem program_trace (r : Fin 8 → Bool) (a s h : List Bool)
    (has : a.length = s.length) (hah : a.length = h.length) :
    ∃ rf, Trace program (8*a.length+4)
      ((data r a s h).withPC (some program.entry))
      ((data rf [] [] []).withPC none) ∧ rf 6 = good a s h := by
  obtain ⟨rf,he,hf⟩ := command_eval r a s h has hah
  exact ⟨rf, by simpa [Nat.add_assoc] using compiled_halt_trace he 0 0, hf⟩

end SubexponentialSAT.SqrtLog.LeafWeightProgram

end OAI.Algorithms
