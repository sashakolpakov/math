import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-! A fixed physical scan merges a current-head assignment with the bucket
representative, keeping the original ambient coordinate order. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

def merge : List Bool → List Bool → List Bool → List Bool
  | [], _, _ => []
  | a::as, hs, bs => (if hs.headD false then a else bs.headD false) ::
      merge as hs.tail bs.tail

@[simp] theorem merge_length (a h b : List Bool) : (merge a h b).length = a.length := by
  induction a generalizing h b with
  | nil => rfl
  | cons a as ih => simp [merge,ih]

theorem merge_ofFn {n : ℕ} (a h b : Fin n → Bool) :
    merge (List.ofFn a) (List.ofFn h) (List.ofFn b) =
      List.ofFn (fun i => if h i then a i else b i) := by
  induction n with
  | zero => simp [merge]
  | succ n ih => simp [List.ofFn_succ,merge,ih]

abbrev Data := StructuredProgram.State 8 5

abbrev tapes (a h b out tmp : List Bool) : Fin 5 → List Bool := ![a,h,b,out,tmp]
abbrev data (r : Fin 8 → Bool) (a h b out tmp : List Bool) : Data :=
  ⟨r,tapes a h b out tmp⟩
def ready (r : Fin 8 → Bool) (a h b out tmp : List Bool) : Data :=
  data (readRegs r 0 3 a.head?) a.tail h b out tmp

abbrev popAssignment : StructuredProgram.Cmd 8 5 := .atom (.pop 0 0 3)
abbrev put : StructuredProgram.Cmd 8 5 :=
  .ite 1 (.atom (.push 4 0)) (.atom (.push 4 2))
abbrev body : StructuredProgram.Cmd 8 5 := .seq (.atom (.pop 1 1 4)) <|
  .seq (.atom (.pop 2 2 5)) (.seq put popAssignment)
abbrev loop : StructuredProgram.Cmd 8 5 := .while 3 body

abbrev scan : StructuredProgram.Cmd 8 5 := .seq popAssignment loop
abbrev command : Cmd 8 5 := .seq (.base scan) (.call (transferProgram 4 3 0 3))

private theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

private theorem popAssignment_eval (r : Fin 8 → Bool) (a h b out tmp : List Bool) :
    StructuredProgram.Eval popAssignment 1 (data r a h b out tmp) (ready r a h b out tmp) := by
  have he := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop 0 0 3) (data r a h b out tmp)
  convert he using 1
  apply state_ext
  · rfl
  · funext i; fin_cases i <;> rfl

private theorem body_eval (r : Fin 8 → Bool) (a h b : Bool)
    (as hs bs out tmp : List Bool) :
    ∃ rf, StructuredProgram.Eval body 5
      (ready r (a::as) (h::hs) (b::bs) out tmp)
      (ready rf as hs bs out ((if h then a else b)::tmp)) := by
  let d0 := ready r (a::as) (h::hs) (b::bs) out tmp
  let d1 := (StructuredProgram.Atom.pop 1 1 4).eval d0
  let d2 := (StructuredProgram.Atom.pop 2 2 5).eval d1
  let d3 := data d2.regs as hs bs out ((if h then a else b)::tmp)
  have ep : StructuredProgram.Eval put 2 d2 d3 := by
    cases h
    · apply StructuredProgram.Eval.ite_false
      · simp [d0,d1,d2,ready,data,tapes,readRegs,StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr,execInstr,StructuredProgram.State.ofCfg
          ]
      · convert StructuredProgram.Eval.atom (StructuredProgram.Atom.push 4 2) d2 using 1
        apply state_ext
        · rfl
        · funext i; fin_cases i <;>
            simp [d0,d1,d2,d3,ready,data,tapes,readRegs,StructuredProgram.Atom.eval,
              StructuredProgram.Atom.instr,execInstr,StructuredProgram.State.ofCfg
              ]
    · apply StructuredProgram.Eval.ite_true
      · simp [d0,d1,d2,ready,data,tapes,readRegs,StructuredProgram.Atom.eval,
          StructuredProgram.Atom.instr,execInstr,StructuredProgram.State.ofCfg
          ]
      · convert StructuredProgram.Eval.atom (StructuredProgram.Atom.push 4 0) d2 using 1
        apply state_ext
        · rfl
        · funext i; fin_cases i <;>
            simp [d0,d1,d2,d3,ready,data,tapes,readRegs,StructuredProgram.Atom.eval,
              StructuredProgram.Atom.instr,execInstr,StructuredProgram.State.ofCfg
              ]
  have ex := popAssignment_eval d2.regs as hs bs out ((if h then a else b)::tmp)
  exact ⟨d2.regs, (StructuredProgram.Eval.atom (.pop 1 1 4) d0).seq
    ((StructuredProgram.Eval.atom (.pop 2 2 5) d1).seq (ep.seq ex))⟩

private theorem loop_eval (r : Fin 8 → Bool) (a h b out tmp : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, StructuredProgram.Eval loop (6*a.length+1) (ready r a h b out tmp)
      (data rf [] [] [] out ((merge a h b).reverse++tmp)) := by
  induction a generalizing r h b tmp with
  | nil =>
    have hh : h=[] := List.length_eq_zero_iff.mp hah.symm
    have hb : b=[] := List.length_eq_zero_iff.mp hab.symm
    subst h; subst b
    exact ⟨readRegs r 0 3 none, StructuredProgram.Eval.while_false
      (by simp [ready,data,readRegs])⟩
  | cons a as ih =>
    cases h with
    | nil => simp at hah
    | cons h hs =>
      cases b with
      | nil => simp at hab
      | cons b bs =>
        obtain ⟨rb,eb⟩ := body_eval r a h b as hs bs out tmp
        obtain ⟨rf,ef⟩ := ih rb hs bs ((if h then a else b)::tmp)
          (by simpa using hah) (by simpa using hab)
        have he := StructuredProgram.Eval.while_true
          (by simp [ready,data,readRegs] : (ready r (a::as) (h::hs) (b::bs) out tmp).regs 3=true)
          eb ef
        refine ⟨rf, ?_⟩
        convert he using 1 <;> simp [merge,List.reverse_cons,List.append_assoc] ; omega

/-- All work inputs are consumed; the forward-order result appears on stack3. -/
theorem command_eval (r : Fin 8 → Bool) (a h b : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Eval command (9*a.length+5) (data r a h b [] [])
      (data rf [] [] [] (merge a h b) []) := by
  obtain ⟨rs,es⟩ := loop_eval r a h b [] [] hah hab
  have ep := popAssignment_eval r a h b [] []
  have esc : Eval (.base scan) (6*a.length+2) (data r a h b [] [])
      (data rs [] [] [] [] (merge a h b).reverse) := by
    have hn : 1 + (6*a.length+1) = 6*a.length+2 := by omega
    simpa only [hn,List.append_nil] using Eval.base (ep.seq es)
  have et := halt_after_trace _
    (transferProgram_trace (4 : Fin 5) 3 (0 : Fin 8) 3 (by decide) (by decide)
      rs (tapes [] [] [] [] (merge a h b).reverse)) 3 rfl rfl
  have hst : transferStacks (4 : Fin 5) 3 (tapes [] [] [] [] (merge a h b).reverse) =
      tapes [] [] [] (merge a h b) [] := by
    funext i
    fin_cases i <;> simp [transferStacks,tapes]
  have eh : Eval (.call (transferProgram 4 3 0 3)) (3*a.length+3)
      (data rs [] [] [] [] (merge a h b).reverse)
      (data (readRegs rs 0 3 none) [] [] [] (merge a h b) []) := by
    apply Eval.call
    dsimp only [transferResult] at et
    rw [hst] at et
    simpa [data,StructuredProgram.State.withPC,transferProgram,tapes,Nat.add_assoc] using et
  exact ⟨readRegs rs 0 3 none, by convert esc.seq eh using 1 ; omega⟩

abbrev program := compiled command 0 3

theorem program_trace (r : Fin 8 → Bool) (a h b : List Bool)
    (hah : a.length=h.length) (hab : a.length=b.length) :
    ∃ rf, Trace program (9*a.length+6)
      ((data r a h b [] []).withPC (some program.entry))
      ((data rf [] [] [] (merge a h b) []).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval r a h b hah hab
  exact ⟨rf, by simpa [Nat.add_assoc] using compiled_halt_trace he 0 3⟩

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

end OAI.Algorithms
