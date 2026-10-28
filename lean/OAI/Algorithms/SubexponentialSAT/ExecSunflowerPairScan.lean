import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSunflowerProgram
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Actual pairwise intersection scanning

The inner scan compares one preserved clause against a runtime list of clauses.
Each comparison calls the concrete intersection-containment program, including
its real membership scans and cleanup. All loops are fixed structured syntax.
-/

namespace SubexponentialSAT.ExecSunflowerPairScan

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

namespace StackOps

variable {r s : ℕ}

abbrev transfer (src dst : Fin s) (v p : Fin r) : Cmd r s :=
  .call (StackRoutines.transferProgram src dst v p)

def transferred (src dst : Fin s) (v p : Fin r) (d : State r s) : State r s :=
  ⟨readRegs d.regs v p none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin s) (v p : Fin r)
    (hs : src ≠ dst) (hr : v ≠ p) (d : State r s) :
    Eval (transfer src dst v p) (3 * (d.stacks src).length + 3) d
      (transferred src dst v p d) := by
  have ht := StackRoutines.transferProgram_trace src dst v p hs hr d.regs d.stacks
  have hh : step (StackRoutines.transferProgram src dst v p)
      (StackRoutines.transferResult 3 src dst v p d.regs d.stacks) =
      some ((transferred src dst v p d).withPC none) := by
    simp [step, StackRoutines.transferResult,
      transferred, StructuredProgram.State.withPC, execInstr]
  exact Eval.call _ (ht.trans (.cons hh (.refl _)))

abbrev copy (src dst tmp : Fin s) (v p : Fin r) : Cmd r s :=
  .call (StackRoutines.copyProgram src dst tmp v p)

def copied (src dst : Fin s) (v p : Fin r) (d : State r s) : State r s :=
  ⟨readRegs d.regs v p none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (src dst tmp : Fin s) (v p : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp) (hr : v ≠ p)
    (d : State r s) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp v p) (7 * (d.stacks src).length + 5) d
      (copied src dst v p d) := by
  have ht := StackRoutines.copyProgram_trace src dst tmp v p hsd hst hdt.symm hr
    d.regs d.stacks htmp
  have hh : step (StackRoutines.copyProgram src dst tmp v p)
      (StackRoutines.copyResult 7 src dst v p d.regs d.stacks) =
      some ((copied src dst v p d).withPC none) := by
    simp [step, StackRoutines.copyResult,
      copied, StructuredProgram.State.withPC, execInstr]
  exact Eval.call _ (ht.trans (.cons hh (.refl _)))

abbrev clear (src : Fin s) (v p : Fin r) : Cmd r s :=
  .call (StackRoutines.clearProgram src v p)

def cleared (src : Fin s) (v p : Fin r) (d : State r s) : State r s :=
  ⟨readRegs d.regs v p none, StackRoutines.clearStacks src d.stacks⟩

theorem clear_eval (src : Fin s) (v p : Fin r) (d : State r s) :
    Eval (clear src v p) (2 * (d.stacks src).length + 3) d (cleared src v p d) := by
  have ht := StackRoutines.clearProgram_trace src v p d.regs d.stacks
  have hh : step (StackRoutines.clearProgram src v p)
      (StackRoutines.clearResult 2 src v p d.regs d.stacks) =
      some ((cleared src v p d).withPC none) := by
    simp [step, StackRoutines.clearResult,
      cleared, StructuredProgram.State.withPC, execInstr]
  exact Eval.call _ (ht.trans (.cons hh (.refl _)))

end StackOps

namespace Against

abbrev Clause := List (List Bool)
abbrev Data := State 14 11

def regs (i : Fin 11) : Fin 14 := Fin.castAdd 3 i
def stackPort (i : Fin 9) : Fin 11 := Fin.castAdd 2 i

theorem regs_injective : Function.Injective regs := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun j : Fin 14 => j.val) h

theorem stacks_injective : Function.Injective stackPort := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun j : Fin 11 => j.val) h

abbrev compare : Cmd 14 11 :=
  .call (ProgramLinking.liftProgram SubexpSunflowerProgram.Intersection.program regs stackPort)

def invariant (C H : Clause) (d : Data) : Prop :=
  d.stacks 10 = Encoding.encodeList id C ∧ d.stacks 8 = Encoding.encodeList id H ∧
  d.stacks 0 = [] ∧ d.stacks 2 = [] ∧ d.stacks 3 = [] ∧ d.stacks 4 = [] ∧
  d.stacks 5 = [] ∧ d.stacks 6 = [] ∧ d.stacks 7 = []

def bad (C H D : Clause) : Bool := C.any (SubexpSunflowerProgram.Intersection.violation D H)

theorem compare_eval (C D H : Clause) (d : Data)
    (hsrc : d.stacks 0 = Encoding.encodeList id C) (hout : d.stacks 1 = [])
    (hD : d.stacks 2 = Encoding.encodeList id D) (hH : d.stacks 8 = Encoding.encodeList id H)
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = [])
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) :
    ∃ n ≤ SubexpSunflowerProgram.Intersection.runBound C D H + 1, ∃ e : Data,
      Eval compare n d e ∧ e.regs 9 = !bad C H D ∧ e.stacks 1 = [!bad C H D] ∧
      (e.stacks 0).length ≤ (Encoding.encodeList id C).length ∧
      e.stacks 2 = d.stacks 2 ∧ e.stacks 8 = d.stacks 8 ∧
      e.stacks 3 = [] ∧ e.stacks 4 = [] ∧ e.stacks 5 = [] ∧
      e.stacks 6 = [] ∧ e.stacks 7 = [] ∧
      e.stacks 9 = d.stacks 9 ∧ e.stacks 10 = d.stacks 10 ∧
      e.regs 11 = d.regs 11 ∧ e.regs 12 = d.regs 12 ∧ e.regs 13 = d.regs 13 := by
  let a := projectState regs stackPort d
  have ha : SubexpSunflowerProgram.Intersection.targets D H a :=
    ⟨hD, hH, h3, h4, h5, h6, h7⟩
  obtain ⟨next, hnxt, n, hn, ht⟩ := SubexpSunflowerProgram.Intersection.program_run
    C D H [] a ha (a.regs 7) (a.regs 8) (a.regs 9)
  have hs : RecordPrograms.state SubexpSunflowerProgram.Intersection.ports a
      (a.regs 7) (a.regs 8) (a.regs 9) (Encoding.encodeList id C ++ []) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, projectState, stackPort,
        SubexpSunflowerProgram.Intersection.ports] using hsrc
    · exact hout
  rw [hs] at ht
  let b := RecordPrograms.state SubexpSunflowerProgram.Intersection.ports next
    false true (!bad C H D)
    (RecordPrograms.unread (SubexpSunflowerProgram.Intersection.violation D H) C [])
    [!bad C H D]
  let e := embedState regs stackPort d b
  have he : Eval compare n d e :=
    eval_call_from_state _ regs stackPort d regs_injective stacks_injective ht
  have hstk (i : Fin 9) : e.stacks (stackPort i) = b.stacks i :=
    embedState_stack _ _ _ _ stacks_injective i
  have hreg (i : Fin 11) : e.regs (regs i) = b.regs i :=
    embedState_register _ _ _ _ regs_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hreg 9).trans (by simp [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports])
  · exact (hstk 1).trans (by simp [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports])
  · change (e.stacks (stackPort 0)).length ≤ _
    rw [hstk]
    simpa [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports] using
      ExecCNFSubset.unread_length_le (SubexpSunflowerProgram.Intersection.violation D H) C
  · change e.stacks (stackPort 2) = _
    rw [hstk]
    simpa [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports, hD] using hnxt.1
  · change e.stacks (stackPort 8) = _
    rw [hstk]
    simpa [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports, hH] using hnxt.2.1
  · exact (hstk 3).trans (by simpa [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports] using hnxt.2.2.1)
  · exact (hstk 4).trans (by simpa [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports] using hnxt.2.2.2.1)
  · exact (hstk 5).trans (by simpa [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports] using hnxt.2.2.2.2.1)
  · exact (hstk 6).trans (by simpa [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports] using hnxt.2.2.2.2.2.1)
  · exact (hstk 7).trans (by simpa [b, RecordPrograms.state, SubexpSunflowerProgram.Intersection.ports] using hnxt.2.2.2.2.2.2)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

abbrev mark : Cmd 14 11 := .base (.atom (.bnot 13 9))
def marked (d : Data) : Data := ⟨Function.update d.regs 13 (!d.regs 9), d.stacks⟩

theorem mark_eval (d : Data) : Eval mark 1 d (marked d) := by
  exact Eval.base (StructuredProgram.Eval.atom (.bnot 13 9) d)

abbrev callback : Cmd 14 11 :=
  .seq (StackOps.transfer 1 2 0 1)
    (.seq (StackOps.copy 10 0 7 0 1)
      (.seq compare (.seq mark (.seq (StackOps.clear 0 0 1)
        (.seq (StackOps.clear 1 0 1) (StackOps.clear 2 0 1))))))

def callbackCost (C H D : Clause) : ℕ :=
  1024 * ((Encoding.encodeList id C).length + 1) *
    ((Encoding.encodeList id D).length + (Encoding.encodeList id H).length + 2)

theorem callback_eval (C D H : Clause) (d : Data)
    (hd : d.stacks 1 = (Encoding.encodeList id D).reverse) (hi : invariant C H d) :
    ∃ n ≤ callbackCost C H D, ∃ e : Data,
      Eval callback n d e ∧ invariant C H e ∧
      e.regs 13 = bad C H D ∧ e.stacks 9 = d.stacks 9 ∧ e.stacks 1 = [] ∧
      e.regs 11 = d.regs 11 ∧ e.regs 12 = d.regs 12 := by
  rcases hi with ⟨hC, hH, h0, h2, h3, h4, h5, h6, h7⟩
  let t := StackOps.transferred 1 2 0 1 d
  let c := StackOps.copied 10 0 0 1 t
  have ht7 : t.stacks 7 = [] := by simp [t, StackOps.transferred, StackRoutines.transferStacks, h7]
  have hc0 : c.stacks 0 = Encoding.encodeList id C := by
    simp [c, t, StackOps.copied, StackOps.transferred, StackRoutines.copyStacks,
      StackRoutines.transferStacks, h0, hC]
  have hc1 : c.stacks 1 = [] := by
    simp [c, t, StackOps.copied, StackOps.transferred, StackRoutines.copyStacks, StackRoutines.transferStacks]
  have hc2 : c.stacks 2 = Encoding.encodeList id D := by
    simp [c, t, StackOps.copied, StackOps.transferred, StackRoutines.copyStacks,
      StackRoutines.transferStacks, h2, hd]
  have hct : c.stacks 8 = Encoding.encodeList id H ∧ c.stacks 3 = [] ∧
      c.stacks 4 = [] ∧ c.stacks 5 = [] ∧ c.stacks 6 = [] ∧ c.stacks 7 = [] := by
    simp [c, t, StackOps.copied, StackOps.transferred, StackRoutines.copyStacks,
      StackRoutines.transferStacks, hH, h3, h4, h5, h6, h7]
  obtain ⟨n, hn, e, he, ha, hp, hl, hD', hH', h3', h4', h5', h6', h7', h9', h10', h11', h12', h13'⟩ :=
    compare_eval C D H c hc0 hc1 hc2 hct.1 hct.2.1 hct.2.2.1 hct.2.2.2.1
      hct.2.2.2.2.1 hct.2.2.2.2.2
  let m := marked e
  let a := StackOps.cleared 0 0 1 m
  let b := StackOps.cleared 1 0 1 a
  let result := StackOps.cleared 2 0 1 b
  refine ⟨(3 * (d.stacks 1).length + 3) + ((7 * (t.stacks 10).length + 5) +
    (n + (1 + ((2 * (m.stacks 0).length + 3) +
      ((2 * (a.stacks 1).length + 3) + (2 * (b.stacks 2).length + 3)))))), ?_, result,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have htC : t.stacks 10 = Encoding.encodeList id C := by
      simp [t, StackOps.transferred, StackRoutines.transferStacks, hC]
    have hbD : b.stacks 2 = Encoding.encodeList id D := by
      simp [b, a, m, marked, StackOps.cleared, StackRoutines.clearStacks, hD', hc2]
    have ha1 : a.stacks 1 = [!bad C H D] := by
      simp [a, m, marked, StackOps.cleared, StackRoutines.clearStacks, hp]
    rw [hd, htC, ha1, hbD]
    simp only [List.length_reverse, List.length_cons, List.length_nil]
    change _ ≤ callbackCost C H D
    dsimp [m, marked] at *
    unfold callbackCost SubexpSunflowerProgram.Intersection.runBound at *
    nlinarith only [hn, hl, Nat.zero_le (Encoding.encodeList id C).length,
      Nat.zero_le (Encoding.encodeList id D).length,
      Nat.zero_le (Encoding.encodeList id H).length]
  · exact Eval.seq (StackOps.transfer_eval 1 2 0 1 (by decide) (by decide) d)
      (Eval.seq (StackOps.copy_eval 10 0 7 0 1 (by decide) (by decide) (by decide)
        (by decide) t ht7) (Eval.seq he (Eval.seq (mark_eval e)
          (Eval.seq (StackOps.clear_eval 0 0 1 m) (Eval.seq (StackOps.clear_eval 1 0 1 a)
            (StackOps.clear_eval 2 0 1 b))))))
  · simp [invariant, result, b, a, m, marked, StackOps.cleared, StackRoutines.clearStacks,
      hH', h3', h4', h5', h6', h7', h10', c, t, StackOps.copied, StackOps.transferred,
      StackRoutines.copyStacks, StackRoutines.transferStacks, hC, hH]
  · simp [result, b, a, m, marked, StackOps.cleared, readRegs, ha]
  · simpa [result, b, a, m, marked, StackOps.cleared, StackRoutines.clearStacks,
      c, t, StackOps.copied, StackOps.transferred, StackRoutines.copyStacks,
      StackRoutines.transferStacks] using h9'
  · simp [result, b, a, StackOps.cleared, StackRoutines.clearStacks]
  · simpa [result, b, a, m, marked, StackOps.cleared, readRegs, c, t,
      StackOps.copied, StackOps.transferred] using h11'
  · simpa [result, b, a, m, marked, StackOps.cleared, readRegs, c, t,
      StackOps.copied, StackOps.transferred] using h12'

def ports : RecordPrograms.Ports 14 11 where
  tag := 11
  present := 12
  found := 13
  source := 9
  payload := 1
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem callback_contract (C H : Clause) :
    RecordMappedPrograms.Contract ports callback (Encoding.encodeList id)
      (bad C H) (callbackCost C H) (invariant C H) := by
  intro D tail base hbase
  let d := RecordPrograms.state ports base false true false tail (Encoding.encodeList id D).reverse
  have hd : d.stacks 1 = (Encoding.encodeList id D).reverse := by simp [d, RecordPrograms.state, ports]
  have hi : invariant C H d := by simpa [invariant, d, RecordPrograms.state, ports] using hbase
  obtain ⟨n, hn, e, he, hi, ha, hs, hp, h11, h12⟩ := callback_eval C D H d hd hi
  have hstate : RecordPrograms.state ports e false true (bad C H D) tail [] = e := by
    apply RecordPrograms.state_eq_self
    · simpa [d, RecordPrograms.state, ports] using h11
    · simpa [d, RecordPrograms.state, ports] using h12
    · exact ha
    · simpa [d, RecordPrograms.state, ports] using hs
    · exact hp
  exact ⟨n, e, hn, hi, by simpa only [hstate] using he⟩

abbrev command : Cmd 14 11 := RecordPrograms.iterate ports callback
def program := compiled command 9 1

theorem command_eval (C H : Clause) (G : List Clause) (suffix : List Bool)
    (base : Data) (hi : invariant C H base) (v pr f : Bool) :
    ∃ n ≤ 3 + RecordMappedPrograms.budget (Encoding.encodeList id) (callbackCost C H) G,
      ∃ next : Data, invariant C H next ∧
      Eval command n
        (RecordPrograms.state ports base v pr f
          (Encoding.encodeList (Encoding.encodeList id) G ++ suffix) [])
        (RecordPrograms.state ports next false true (G.any (bad C H))
          (RecordMappedPrograms.unread (Encoding.encodeList id) (bad C H) G suffix) []) := by
  obtain ⟨n, next, hn, hi, he⟩ := RecordMappedPrograms.iterate_run ports callback
    (Encoding.encodeList id) (bad C H) (callbackCost C H) (invariant C H)
    (callback_contract C H) G suffix base hi v pr f
  exact ⟨n, hn, next, hi, he⟩

theorem no_bad_iff (C H : Clause) (G : List Clause) :
    G.any (bad C H) = false ↔
      ∀ D ∈ G, SubexpSunflowerProgram.Intersection.ContainsIntersection C D H := by
  simp only [List.any_eq_false]
  constructor
  · intro h D hD
    apply (SubexpSunflowerProgram.Intersection.no_violation_iff C D H).mp
    simpa [bad] using h D hD
  · intro h D hD
    simpa [bad] using (SubexpSunflowerProgram.Intersection.no_violation_iff C D H).mpr (h D hD)

def runBound (C H : Clause) (G : List Clause) : ℕ :=
  (1024 * ((Encoding.encodeList id C).length + 1) +
    1024 * ((Encoding.encodeList id C).length + 1) *
      ((Encoding.encodeList id H).length + 2) + 17) *
    ((Encoding.encodeList (Encoding.encodeList id) G).length + 1)

theorem program_run (C H : Clause) (G : List Clause) (suffix : List Bool)
    (base : Data) (hi : invariant C H base) (v pr f : Bool) :
    ∃ next : Data, invariant C H next ∧
      RunsIn program (runBound C H G)
        ((RecordPrograms.state ports base v pr f
          (Encoding.encodeList (Encoding.encodeList id) G ++ suffix) []).withPC (some program.entry))
        ((RecordPrograms.state ports next false true (G.any (bad C H))
          (RecordMappedPrograms.unread (Encoding.encodeList id) (bad C H) G suffix) []).withPC none) := by
  obtain ⟨n, hn, next, hi, he⟩ := command_eval C H G suffix base hi v pr f
  have hb := RecordMappedPrograms.program_budget_le_input (Encoding.encodeList id)
    (callbackCost C H) G (1024 * ((Encoding.encodeList id C).length + 1))
    (1024 * ((Encoding.encodeList id C).length + 1) *
      ((Encoding.encodeList id H).length + 2)) (by
        intro D hD
        unfold callbackCost
        nlinarith)
  exact ⟨next, hi, n + 1, by unfold runBound; omega, compiled_halt_trace he 9 1⟩

end Against

namespace AllPairs

abbrev Clause := Against.Clause
abbrev Data := State 17 13

def regs (i : Fin 14) : Fin 17 := Fin.castAdd 3 i
def stackPort (i : Fin 11) : Fin 13 := Fin.castAdd 2 i

theorem regs_injective : Function.Injective regs := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun j : Fin 17 => j.val) h

theorem stacks_injective : Function.Injective stackPort := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun j : Fin 13 => j.val) h

abbrev scanTail : Cmd 17 13 := .call (ProgramLinking.liftProgram Against.program regs stackPort)

theorem scanTail_eval (C H : Clause) (G : List Clause) (d : Data)
    (hg : d.stacks 9 = Encoding.encodeList (Encoding.encodeList id) G)
    (hp : d.stacks 1 = [])
    (hi : Against.invariant C H (projectState regs stackPort d)) :
    ∃ n ≤ Against.runBound C H G, ∃ e : Data,
      Eval scanTail n d e ∧ Against.invariant C H (projectState regs stackPort e) ∧
      e.regs 13 = G.any (Against.bad C H) ∧ e.stacks 1 = [] ∧
      (e.stacks 9).length ≤ (Encoding.encodeList (Encoding.encodeList id) G).length ∧
      e.stacks 11 = d.stacks 11 ∧ e.stacks 12 = d.stacks 12 ∧
      e.regs 14 = d.regs 14 ∧ e.regs 15 = d.regs 15 ∧ e.regs 16 = d.regs 16 := by
  let a := projectState regs stackPort d
  obtain ⟨next, hnxt, n, hn, ht⟩ := Against.program_run C H G [] a hi
    (a.regs 11) (a.regs 12) (a.regs 13)
  have hs : RecordPrograms.state Against.ports a (a.regs 11) (a.regs 12) (a.regs 13)
      (Encoding.encodeList (Encoding.encodeList id) G ++ []) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simpa [a, projectState, stackPort, Against.ports] using hg
    · exact hp
  rw [hs] at ht
  let b := RecordPrograms.state Against.ports next false true (G.any (Against.bad C H))
    (RecordMappedPrograms.unread (Encoding.encodeList id) (Against.bad C H) G []) []
  let e := embedState regs stackPort d b
  have he : Eval scanTail n d e :=
    eval_call_from_state _ regs stackPort d regs_injective stacks_injective ht
  have hstk (i : Fin 11) : e.stacks (stackPort i) = b.stacks i :=
    embedState_stack _ _ _ _ stacks_injective i
  have hreg (i : Fin 14) : e.regs (regs i) = b.regs i :=
    embedState_register _ _ _ _ regs_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh : projectState regs stackPort e = b :=
      projectState_embed regs stackPort d b regs_injective stacks_injective
    rw [hh]
    simpa [b, Against.invariant, RecordPrograms.state, Against.ports] using hnxt
  · exact (hreg 13).trans (by simp [b, RecordPrograms.state, Against.ports])
  · exact (hstk 1).trans (by simp [b, RecordPrograms.state, Against.ports])
  · change (e.stacks (stackPort 9)).length ≤ _
    rw [hstk]
    simpa [b, RecordPrograms.state, Against.ports] using
      RecordMappedPrograms.unread_length_le (Encoding.encodeList id) (Against.bad C H) G []
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

def invariant (H : Clause) (d : Data) : Prop :=
  d.stacks 8 = Encoding.encodeList id H ∧
    ∀ i : Fin 11, i ≠ 8 → d.stacks (stackPort i) = []

abbrev mark : Cmd 17 13 := .base (.atom (.copy 16 13))
def marked (d : Data) : Data := ⟨Function.update d.regs 16 (d.regs 13), d.stacks⟩

theorem mark_eval (d : Data) : Eval mark 1 d (marked d) := by
  exact Eval.base (StructuredProgram.Eval.atom (.copy 16 13) d)

abbrev callback : Cmd 17 13 :=
  .seq (StackOps.transfer 12 10 0 1) (.seq (StackOps.copy 11 9 7 0 1)
    (.seq scanTail (.seq mark (.seq (StackOps.clear 9 0 1) (StackOps.clear 10 0 1)))))

def callbackCost (C H : Clause) (G : List Clause) : ℕ :=
  Against.runBound C H G + 20 * ((Encoding.encodeList id C).length +
    (Encoding.encodeList (Encoding.encodeList id) G).length + 2)

theorem callback_eval (C H : Clause) (G : List Clause) (d : Data)
    (hC : d.stacks 12 = (Encoding.encodeList id C).reverse)
    (hG : d.stacks 11 = Encoding.encodeList (Encoding.encodeList id) G)
    (hi : invariant H d) :
    ∃ n ≤ callbackCost C H G, ∃ e : Data,
      Eval callback n d e ∧ invariant H e ∧
      e.regs 16 = G.any (Against.bad C H) ∧ e.stacks 11 = d.stacks 11 ∧
      e.stacks 12 = [] ∧ e.regs 14 = d.regs 14 ∧ e.regs 15 = d.regs 15 := by
  rcases hi with ⟨hH, hwork⟩
  have h0 := hwork 0 (by decide)
  have h1 := hwork 1 (by decide)
  have h2 := hwork 2 (by decide)
  have h3 := hwork 3 (by decide)
  have h4 := hwork 4 (by decide)
  have h5 := hwork 5 (by decide)
  have h6 := hwork 6 (by decide)
  have h7 := hwork 7 (by decide)
  have h9 := hwork 9 (by decide)
  have h10 := hwork 10 (by decide)
  let t := StackOps.transferred 12 10 0 1 d
  let c := StackOps.copied 11 9 0 1 t
  have ht7 : t.stacks 7 = [] := by
    simpa [t, StackOps.transferred, StackRoutines.transferStacks, stackPort] using h7
  have hcG : c.stacks 9 = Encoding.encodeList (Encoding.encodeList id) G := by
    simp [c, t, StackOps.copied, StackOps.transferred, StackRoutines.copyStacks,
      StackRoutines.transferStacks, hG, show d.stacks 9 = [] from h9]
  have hcP : c.stacks 1 = [] := by
    simpa [c, t, StackOps.copied, StackOps.transferred, StackRoutines.copyStacks,
      StackRoutines.transferStacks, stackPort] using h1
  have hcI : Against.invariant C H (projectState regs stackPort c) := by
    simp [Against.invariant, c, t, projectState, stackPort, StackOps.copied,
      StackOps.transferred, StackRoutines.copyStacks, StackRoutines.transferStacks,
      hC, hH, show d.stacks 10 = [] from h10, show d.stacks 0 = [] from h0,
      show d.stacks 2 = [] from h2, show d.stacks 3 = [] from h3,
      show d.stacks 4 = [] from h4, show d.stacks 5 = [] from h5,
      show d.stacks 6 = [] from h6, show d.stacks 7 = [] from h7]
  obtain ⟨n, hn, e, he, hei, ha, hp, hglen, h11, h12, h14, h15, h16⟩ :=
    scanTail_eval C H G c hcG hcP hcI
  let m := marked e
  let a := StackOps.cleared 9 0 1 m
  let result := StackOps.cleared 10 0 1 a
  have he10 : e.stacks 10 = Encoding.encodeList id C := hei.1
  refine ⟨(3 * (d.stacks 12).length + 3) + ((7 * (t.stacks 11).length + 5) +
    (n + (1 + ((2 * (m.stacks 9).length + 3) + (2 * (a.stacks 10).length + 3))))),
    ?_, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have htG : t.stacks 11 = Encoding.encodeList (Encoding.encodeList id) G := by
      simp [t, StackOps.transferred, StackRoutines.transferStacks, hG]
    rw [hC, htG]
    simp only [List.length_reverse]
    have ha10 : a.stacks 10 = Encoding.encodeList id C := by
      simp [a, m, marked, StackOps.cleared, StackRoutines.clearStacks, he10]
    rw [ha10]
    change _ ≤ callbackCost C H G
    dsimp [m, marked]
    unfold callbackCost
    omega
  · exact Eval.seq (StackOps.transfer_eval 12 10 0 1 (by decide) (by decide) d)
      (Eval.seq (StackOps.copy_eval 11 9 7 0 1 (by decide) (by decide) (by decide)
        (by decide) t ht7) (Eval.seq he (Eval.seq (mark_eval e)
          (Eval.seq (StackOps.clear_eval 9 0 1 m) (StackOps.clear_eval 10 0 1 a)))))
  · refine ⟨?_, ?_⟩
    · simpa [result, a, m, marked, StackOps.cleared, StackRoutines.clearStacks,
        projectState, stackPort] using hei.2.1
    · intro i hi
      rcases hei with ⟨_, _, he0, he2, he3, he4, he5, he6, he7⟩
      fin_cases i <;>
        simp_all [result, a, m, marked, StackOps.cleared, StackRoutines.clearStacks,
          projectState, stackPort]
  · simp [result, a, m, marked, StackOps.cleared, readRegs, ha]
  · simpa [result, a, m, marked, StackOps.cleared, StackRoutines.clearStacks,
      c, t, StackOps.copied, StackOps.transferred, StackRoutines.copyStacks,
      StackRoutines.transferStacks] using h11
  · simpa [result, a, m, marked, StackOps.cleared, StackRoutines.clearStacks,
      c, t, StackOps.copied, StackOps.transferred, StackRoutines.copyStacks,
      StackRoutines.transferStacks] using h12
  · simpa [result, a, m, marked, StackOps.cleared, readRegs, c, t,
      StackOps.copied, StackOps.transferred] using h14
  · simpa [result, a, m, marked, StackOps.cleared, readRegs, c, t,
      StackOps.copied, StackOps.transferred] using h15

def ports : RecordPrograms.Ports 17 13 where
  tag := 14
  present := 15
  found := 16
  source := 11
  payload := 12
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem callback_contract (C H : Clause) (G : List Clause) (base : Data)
    (hi : invariant H base) :
    ∃ n ≤ callbackCost C H G, ∃ next : Data, invariant H next ∧
      Eval callback n
        (RecordPrograms.state ports base false true false
          (Encoding.encodeList (Encoding.encodeList id) G) (Encoding.encodeList id C).reverse)
        (RecordPrograms.state ports next false true (G.any (Against.bad C H))
          (Encoding.encodeList (Encoding.encodeList id) G) []) := by
  let d := RecordPrograms.state ports base false true false
    (Encoding.encodeList (Encoding.encodeList id) G) (Encoding.encodeList id C).reverse
  have hdC : d.stacks 12 = (Encoding.encodeList id C).reverse := by simp [d, RecordPrograms.state, ports]
  have hdG : d.stacks 11 = Encoding.encodeList (Encoding.encodeList id) G := by simp [d, RecordPrograms.state, ports]
  have hdi : invariant H d := by
    refine ⟨?_, ?_⟩
    · simpa [d, RecordPrograms.state, ports] using hi.1
    · intro i h
      have hx := hi.2 i h
      fin_cases i <;> simpa [d, RecordPrograms.state, ports, stackPort] using hx
  obtain ⟨n, hn, e, he, hi, ha, hs, hp, h14, h15⟩ := callback_eval C H G d hdC hdG hdi
  have hstate : RecordPrograms.state ports e false true (G.any (Against.bad C H))
      (Encoding.encodeList (Encoding.encodeList id) G) [] = e := by
    apply RecordPrograms.state_eq_self
    · simpa [d, RecordPrograms.state, ports] using h14
    · simpa [d, RecordPrograms.state, ports] using h15
    · exact ha
    · simpa [d, RecordPrograms.state, ports] using hs
    · exact hp
  exact ⟨n, hn, e, hi, by simpa only [hstate] using he⟩

abbrev badPairs (H : Clause) : List Clause → Bool
  | [] => false
  | C :: G => G.any (Against.bad C H) || badPairs H G

abbrev unread (H : Clause) : List Clause → List Bool
  | [] => []
  | C :: G => if G.any (Against.bad C H) then
      Encoding.encodeList (Encoding.encodeList id) G else unread H G

abbrev budget (H : Clause) : List Clause → ℕ
  | [] => 0
  | C :: G => 6 * (Encoding.encodeList id C).length + callbackCost C H G + 7 + budget H G

abbrev command : Cmd 17 13 := RecordPrograms.iterate ports callback
def program := compiled command 11 12

theorem loop_run (H : Clause) (G : List Clause) (base : Data) (hi : invariant H base) :
    ∃ n ≤ 1 + budget H G, ∃ next : Data, invariant H next ∧
      Eval (RecordPrograms.loop ports callback) n
        (RecordMappedPrograms.afterTag ports (Encoding.encodeList id) base G [])
        (RecordPrograms.state ports next false true (badPairs H G) (unread H G) []) := by
  induction G generalizing base with
  | nil =>
      refine ⟨1, by simp [budget], base, hi, ?_⟩
      exact Eval.while_false (by simp [RecordMappedPrograms.afterTag])
  | cons C G ih =>
      obtain ⟨n, hn, middle, hm, hc⟩ := callback_contract C H G base hi
      have hr : Eval (RecordPrograms.reader ports) (6 * (Encoding.encodeList id C).length + 4)
          (RecordMappedPrograms.afterTag ports (Encoding.encodeList id) base (C :: G) [])
          (RecordPrograms.state ports base false true false
            (Encoding.encodeList (Encoding.encodeList id) G) (Encoding.encodeList id C).reverse) := by
        simpa [RecordMappedPrograms.afterTag] using RecordPrograms.reader_eval ports base
          (Encoding.encodeList id C) (Encoding.encodeList (Encoding.encodeList id) G) [] true true false
      have hg : (RecordMappedPrograms.afterTag ports (Encoding.encodeList id) base (C :: G) []).regs
          ports.tag = true := by simp [RecordMappedPrograms.afterTag]
      cases hb : G.any (Against.bad C H) with
      | true =>
          have hbranch : Eval
              (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
                (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
              (RecordPrograms.state ports middle false true (G.any (Against.bad C H))
                (Encoding.encodeList (Encoding.encodeList id) G) [])
              (RecordPrograms.state ports middle false true true
                (Encoding.encodeList (Encoding.encodeList id) G) []) := by
            rw [hb]
            exact Eval.ite_true (by simp) (RecordPrograms.set_tag_eval ports middle
              false true true false _ [])
          have hbody := Eval.seq hr (Eval.seq hc hbranch)
          have hend : Eval (RecordPrograms.loop ports callback) 1
              (RecordPrograms.state ports middle false true true
                (Encoding.encodeList (Encoding.encodeList id) G) [])
              (RecordPrograms.state ports middle false true true
                (Encoding.encodeList (Encoding.encodeList id) G) []) := Eval.while_false (by simp)
          refine ⟨(6 * (Encoding.encodeList id C).length + 4 + (n + 2)) + 1 + 1,
            by simp only [budget]; omega, middle, hm, ?_⟩
          simpa [RecordPrograms.loop, RecordPrograms.body, badPairs, unread, hb] using
            Eval.while_true hg hbody hend
      | false =>
          have hbranch : Eval
              (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
                (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
              (RecordPrograms.state ports middle false true (G.any (Against.bad C H))
                (Encoding.encodeList (Encoding.encodeList id) G) [])
              (RecordMappedPrograms.afterTag ports (Encoding.encodeList id) middle G []) := by
            rw [hb]
            apply Eval.ite_false (by simp)
            simpa using RecordMappedPrograms.pop_list_eval ports (Encoding.encodeList id)
              middle G [] false true
          have hbody := Eval.seq hr (Eval.seq hc hbranch)
          obtain ⟨m, hmn, next, hnext, hrest⟩ := ih middle hm
          refine ⟨(6 * (Encoding.encodeList id C).length + 4 + (n + 2)) + m + 1,
            by simp only [budget]; omega, next, hnext, ?_⟩
          simpa [RecordPrograms.loop, RecordPrograms.body, badPairs, unread, hb] using
            Eval.while_true hg hbody hrest

theorem command_eval (H : Clause) (G : List Clause) (base : Data)
    (hi : invariant H base) (v pr f : Bool) :
    ∃ n ≤ 3 + budget H G, ∃ next : Data, invariant H next ∧
      Eval command n
        (RecordPrograms.state ports base v pr f (Encoding.encodeList (Encoding.encodeList id) G) [])
        (RecordPrograms.state ports next false true (badPairs H G) (unread H G) []) := by
  obtain ⟨n, hn, next, hi, ht⟩ := loop_run H G base hi
  refine ⟨1 + (1 + n), by omega, next, hi, ?_⟩
  exact Eval.seq (RecordPrograms.set_found_eval ports base v pr f false _ [])
    (Eval.seq (by simpa using (RecordMappedPrograms.pop_list_eval ports (Encoding.encodeList id) base G [] v pr)) ht)

theorem no_badPairs_iff (H : Clause) (G : List Clause) :
    badPairs H G = false ↔
      G.Pairwise (fun C D => SubexpSunflowerProgram.Intersection.ContainsIntersection C D H) := by
  induction G with
  | nil => simp [badPairs]
  | cons C G ih =>
      simp only [badPairs, Bool.or_eq_false_iff, Against.no_bad_iff, ih, List.pairwise_cons]

theorem budget_le (H : Clause) (G : List Clause) (N : ℕ)
    (hN : (Encoding.encodeList (Encoding.encodeList id) G).length ≤ N) :
    budget H G ≤ G.length *
      ((1024 * ((Encoding.encodeList id H).length + 3) + 70) * (N + 1)^2) := by
  induction G with
  | nil => simp [budget]
  | cons C G ih =>
      have hshape : 2 * (Encoding.encodeList id C).length + 2 +
          (Encoding.encodeList (Encoding.encodeList id) G).length ≤ N := by
        simpa only [Encoding.length_encodeList_cons] using hN
      have hC : (Encoding.encodeList id C).length ≤ N := by omega
      have hG : (Encoding.encodeList (Encoding.encodeList id) G).length ≤ N := by omega
      have ht := ih hG
      have ha : Against.runBound C H G ≤
          (1024 * (N + 1) * ((Encoding.encodeList id H).length + 3) + 17) * (N + 1) := by
        unfold Against.runBound
        calc
          _ = (1024 * ((Encoding.encodeList id C).length + 1) *
              ((Encoding.encodeList id H).length + 3) + 17) *
              ((Encoding.encodeList (Encoding.encodeList id) G).length + 1) := by ring
          _ ≤ _ := by gcongr
      have hs : 6 * (Encoding.encodeList id C).length + callbackCost C H G + 7 ≤
          (1024 * ((Encoding.encodeList id H).length + 3) + 70) * (N + 1)^2 := by
        unfold callbackCost
        nlinarith
      simp only [budget, List.length_cons]
      nlinarith

def polynomialBound (H : Clause) (G : List Clause) : ℕ :=
  4 + (1024 * ((Encoding.encodeList id H).length + 3) + 70) *
    ((Encoding.encodeList (Encoding.encodeList id) G).length + 1)^3

theorem budget_le_polynomial (H : Clause) (G : List Clause) :
    4 + budget H G ≤ polynomialBound H G := by
  let N := (Encoding.encodeList (Encoding.encodeList id) G).length
  have hb := budget_le H G N (by rfl)
  have hl : G.length ≤ N + 1 := by
    have ht := Encoding.length_encodeList_lower (Encoding.encodeList id) G
    dsimp [N]
    omega
  calc
    4 + budget H G ≤ 4 + G.length *
        ((1024 * ((Encoding.encodeList id H).length + 3) + 70) * (N + 1)^2) := by omega
    _ ≤ 4 + (N + 1) *
        ((1024 * ((Encoding.encodeList id H).length + 3) + 70) * (N + 1)^2) := by gcongr
    _ = polynomialBound H G := by unfold polynomialBound; dsimp [N]; ring

/-- The nested pair scan is one finite program. The bound includes both scans,
all copies, failed comparisons, and the final return. -/
theorem program_run (H : Clause) (G : List Clause) (base : Data)
    (hi : invariant H base) (v pr f : Bool) :
    ∃ next : Data, invariant H next ∧
      RunsIn program (polynomialBound H G)
        ((RecordPrograms.state ports base v pr f
          (Encoding.encodeList (Encoding.encodeList id) G) []).withPC (some program.entry))
        ((RecordPrograms.state ports next false true (badPairs H G) (unread H G) []).withPC none) := by
  obtain ⟨n, hn, next, hi, he⟩ := command_eval H G base hi v pr f
  exact ⟨next, hi, n + 1, by have := budget_le_polynomial H G; omega,
    compiled_halt_trace he 11 12⟩

theorem primitive_run (H : Clause) (G : List Clause) (base : Data)
    (hi : invariant H base) (v pr f : Bool) :
    ∃ next : Data, invariant H next ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * polynomialBound H G)
        (primitiveCfg program ((RecordPrograms.state ports base v pr f
          (Encoding.encodeList (Encoding.encodeList id) G) []).withPC (some program.entry)))
        (primitiveCfg program ((RecordPrograms.state ports next false true (badPairs H G)
          (unread H G) []).withPC none)) := by
  obtain ⟨next, hi, ht⟩ := program_run H G base hi v pr f
  exact ⟨next, hi, BitProgram.primitive_execution program ht⟩

end AllPairs
end SubexponentialSAT.ExecSunflowerPairScan

end OAI.Algorithms
