import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerPairScan
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScanPreserve
import OAI.Algorithms.SubexponentialSAT.FamilySizeGuardProgram

namespace OAI.Algorithms

/-!
# Fixed-port composition for the encoded sunflower candidate checker

Persistent inputs are the core on stack 8, selected family on stack 13, and
binary width and size thresholds on stacks 14 and 15. The larger caller has
one register outside every component's footprint for the accumulated result.
-/

namespace SubexponentialSAT.ExecSunflowerCandidateProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open ExecSunflowerPairScan

abbrev Clause := List (List Bool)
abbrev Formula := List Clause
abbrev Data := State 18 16

def Clean (d : Data) : Prop :=
  ∀ i : Fin 13, i ≠ 8 → d.stacks (Fin.castAdd 3 i) = []

def Ready (G : Formula) (H : Clause) (width size : List Bool) (d : Data) : Prop :=
  d.stacks 13 = Encoding.encodeList (Encoding.encodeList id) G ∧
  d.stacks 8 = Encoding.encodeList id H ∧ d.stacks 14 = width ∧
  d.stacks 15 = size ∧ Clean d

namespace PairCall

def regPort (i : Fin 17) : Fin 18 := i.castSucc
def stackPort (i : Fin 13) : Fin 16 := Fin.castAdd 3 i

theorem reg_injective : Function.Injective regPort := Fin.castSucc_injective 17
theorem stack_injective : Function.Injective stackPort := Fin.castAdd_injective 13 3

abbrev call : Cmd 18 16 := .call
  (ProgramLinking.liftProgram ExecSunflowerPairScan.AllPairs.program regPort stackPort)

theorem unread_length_le (H : Clause) (G : Formula) :
    (ExecSunflowerPairScan.AllPairs.unread H G).length ≤
      (Encoding.encodeList (Encoding.encodeList id) G).length := by
  induction G with
  | nil => simp [ExecSunflowerPairScan.AllPairs.unread, Encoding.encodeList]
  | cons C G ih =>
      cases hb : G.any (ExecSunflowerPairScan.Against.bad C H) <;>
        simp [ExecSunflowerPairScan.AllPairs.unread, hb, Encoding.length_encodeList_cons] ; omega

theorem call_eval (G : Formula) (H : Clause) (d : Data)
    (hG : d.stacks 11 = Encoding.encodeList (Encoding.encodeList id) G)
    (hout : d.stacks 12 = [])
    (hi : ExecSunflowerPairScan.AllPairs.invariant H (projectState regPort stackPort d)) :
    ∃ n ≤ ExecSunflowerPairScan.AllPairs.polynomialBound H G, ∃ e : Data,
      Eval call n d e ∧
      ExecSunflowerPairScan.AllPairs.invariant H (projectState regPort stackPort e) ∧
      e.regs 16 = ExecSunflowerPairScan.AllPairs.badPairs H G ∧ e.regs 17 = d.regs 17 ∧
      e.stacks 12 = [] ∧
      (e.stacks 11).length ≤ (Encoding.encodeList (Encoding.encodeList id) G).length ∧
      e.stacks 13 = d.stacks 13 ∧ e.stacks 14 = d.stacks 14 ∧ e.stacks 15 = d.stacks 15 := by
  let a := projectState regPort stackPort d
  obtain ⟨next, hnxt, n, hn, ht⟩ := ExecSunflowerPairScan.AllPairs.program_run H G a hi
    (a.regs 14) (a.regs 15) (a.regs 16)
  have hs : RecordPrograms.state ExecSunflowerPairScan.AllPairs.ports a
      (a.regs 14) (a.regs 15) (a.regs 16)
      (Encoding.encodeList (Encoding.encodeList id) G) [] = a := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · exact hG
    · exact hout
  rw [hs] at ht
  let b := RecordPrograms.state ExecSunflowerPairScan.AllPairs.ports next false true
    (ExecSunflowerPairScan.AllPairs.badPairs H G) (ExecSunflowerPairScan.AllPairs.unread H G) []
  let e := embedState regPort stackPort d b
  have he : Eval call n d e :=
    eval_call_from_state _ regPort stackPort d reg_injective stack_injective ht
  have hstk (i : Fin 13) : e.stacks (stackPort i) = b.stacks i :=
    embedState_stack _ _ _ _ stack_injective i
  have hreg (i : Fin 17) : e.regs (regPort i) = b.regs i :=
    embedState_register _ _ _ _ reg_injective i
  refine ⟨n, hn, e, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh : projectState regPort stackPort e = b :=
      projectState_embed regPort stackPort d b reg_injective stack_injective
    rw [hh]
    refine ⟨?_, ?_⟩
    · simpa [b, RecordPrograms.state, ExecSunflowerPairScan.AllPairs.ports] using hnxt.1
    · intro i h
      have hh := hnxt.2 i h
      fin_cases i <;> simpa [b, RecordPrograms.state, ExecSunflowerPairScan.AllPairs.ports,
        ExecSunflowerPairScan.AllPairs.stackPort] using hh
  · exact (hreg 16).trans (by simp [b, RecordPrograms.state, ExecSunflowerPairScan.AllPairs.ports])
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact (hstk 12).trans (by simp [b, RecordPrograms.state, ExecSunflowerPairScan.AllPairs.ports])
  · change (e.stacks (stackPort 11)).length ≤ _
    rw [hstk]
    simpa [b, RecordPrograms.state, ExecSunflowerPairScan.AllPairs.ports] using unread_length_le H G
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)

abbrev command : Cmd 18 16 :=
  .seq (StackOps.copy 13 11 7 0 1) (.seq call (StackOps.clear 11 0 1))

def bound (G : Formula) (H : Clause) : ℕ :=
  ExecSunflowerPairScan.AllPairs.polynomialBound H G +
    9 * (Encoding.encodeList (Encoding.encodeList id) G).length + 8

theorem command_eval (G : Formula) (H : Clause) (width size : List Bool) (d : Data)
    (hi : Ready G H width size d) :
    ∃ n ≤ bound G H, ∃ e : Data, Eval command n d e ∧ Ready G H width size e ∧
      e.regs 16 = ExecSunflowerPairScan.AllPairs.badPairs H G ∧ e.regs 17 = d.regs 17 := by
  rcases hi with ⟨hG, hH, hw, hz, hc⟩
  let c := StackOps.copied 13 11 0 1 d
  have h7 : d.stacks 7 = [] := hc 7 (by decide)
  have h11 : d.stacks 11 = [] := hc 11 (by decide)
  have hcG : c.stacks 11 = Encoding.encodeList (Encoding.encodeList id) G := by
    simp [c, StackOps.copied, StackRoutines.copyStacks, h11, hG]
  have hc12 : c.stacks 12 = [] := by
    simpa [c, StackOps.copied, StackRoutines.copyStacks] using hc 12 (by decide)
  have hci : ExecSunflowerPairScan.AllPairs.invariant H (projectState regPort stackPort c) := by
    refine ⟨?_, ?_⟩
    · simpa [c, StackOps.copied, StackRoutines.copyStacks, projectState, stackPort] using hH
    · intro i hh
      have hclean := hc (Fin.castAdd 2 i) (by
        intro h; apply hh; exact Fin.ext (congrArg (fun j : Fin 13 => j.val) h))
      fin_cases i <;> simpa [c, StackOps.copied, StackRoutines.copyStacks,
        projectState, stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean
  obtain ⟨n, hn, e, he, hei, ha, hf, hp, hlen, h13, h14, h15⟩ := call_eval G H c hcG hc12 hci
  let result := StackOps.cleared 11 0 1 e
  refine ⟨(7 * (d.stacks 13).length + 5) + (n + (2 * (e.stacks 11).length + 3)),
    ?_, result, ?_, ?_, ?_, ?_⟩
  · rw [hG]
    unfold bound
    omega
  · exact Eval.seq (StackOps.copy_eval 13 11 7 0 1 (by decide) (by decide) (by decide)
      (by decide) d h7) (Eval.seq he (StackOps.clear_eval 11 0 1 e))
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [result, StackOps.cleared, StackRoutines.clearStacks, h13, c,
        StackOps.copied, StackRoutines.copyStacks, hG]
    · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState, stackPort] using hei.1
    · simp [result, StackOps.cleared, StackRoutines.clearStacks, h14, c,
        StackOps.copied, StackRoutines.copyStacks, hw]
    · simp [result, StackOps.cleared, StackRoutines.clearStacks, h15, c,
        StackOps.copied, StackRoutines.copyStacks, hz]
    · intro i hh
      have hclean := hei.2
      fin_cases i
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 0 (by decide)
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 1 (by decide)
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 2 (by decide)
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 3 (by decide)
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 4 (by decide)
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 5 (by decide)
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 6 (by decide)
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 7 (by decide)
      · exact False.elim (hh rfl)
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 9 (by decide)
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hclean 10 (by decide)
      · simp [result, StackOps.cleared, StackRoutines.clearStacks]
      · simpa [result, StackOps.cleared, StackRoutines.clearStacks, projectState,
          stackPort, ExecSunflowerPairScan.AllPairs.stackPort] using hp
  · simpa [result, StackOps.cleared, readRegs] using ha
  · simpa [result, StackOps.cleared, readRegs, c, StackOps.copied] using hf

end PairCall

namespace CoreCall

def regPort (i : Fin 15) : Fin 18 := Fin.castAdd 3 i
def stackPort (i : Fin 13) : Fin 16 :=
  if i = 12 then 13 else if i = 9 then 8 else if i = 8 then 9 else Fin.castAdd 3 i

theorem reg_injective : Function.Injective regPort := Fin.castAdd_injective 15 3
theorem stack_injective : Function.Injective stackPort := by decide

def missing (G : Formula) (H : Clause) : Bool :=
  G.any (fun C => ExecClauseRelationScan.test .missingCore C H)

abbrev call : Cmd 18 16 := .call (ProgramLinking.liftProgram
  (ExecClauseRelationScan.Preserving.program .missingCore) regPort stackPort)

private theorem local_stacks (G : Formula) (H : Clause)
    (a b : State 15 13)
    (ha : ExecClauseRelationScan.Preserving.invariant G H a)
    (hb : ExecClauseRelationScan.Preserving.invariant G H b)
    (hout : b.stacks 11 = [missing G H]) :
    b.stacks = Function.update a.stacks 11 [missing G H] := by
  have haw (i : Fin 9) : a.stacks (Fin.castAdd 4 i) = [] := ha.2.1.2 i
  have hbw (i : Fin 9) : b.stacks (Fin.castAdd 4 i) = [] := hb.2.1.2 i
  funext i
  fin_cases i
  · simpa using (hbw 0).trans (haw 0).symm
  · simpa using (hbw 1).trans (haw 1).symm
  · simpa using (hbw 2).trans (haw 2).symm
  · simpa using (hbw 3).trans (haw 3).symm
  · simpa using (hbw 4).trans (haw 4).symm
  · simpa using (hbw 5).trans (haw 5).symm
  · simpa using (hbw 6).trans (haw 6).symm
  · simpa using (hbw 7).trans (haw 7).symm
  · simpa using (hbw 8).trans (haw 8).symm
  · simpa [ExecClauseRelationScan.Preserving.restrict,
      ExecClauseRelationScan.Preserving.stackPort] using hb.2.1.1.trans ha.2.1.1.symm
  · simpa using hb.2.2.trans ha.2.2.symm
  · simpa using hout
  · simpa using hb.1.trans ha.1.symm

theorem call_eval (G : Formula) (H : Clause) (width size : List Bool) (d : Data)
    (hi : Ready G H width size d) :
    ∃ n ≤ ExecClauseRelationScan.Preserving.bound G H, ∃ e : Data,
      Eval call n d e ∧ e.stacks = Function.update d.stacks 11 [missing G H] ∧
      e.regs 14 = missing G H ∧ e.regs 17 = d.regs 17 := by
  let a := projectState regPort stackPort d
  have ha : ExecClauseRelationScan.Preserving.invariant G H a := by
    refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
    · exact hi.1
    · exact hi.2.1
    · intro i
      fin_cases i
      · exact hi.2.2.2.2 0 (by decide)
      · exact hi.2.2.2.2 1 (by decide)
      · exact hi.2.2.2.2 2 (by decide)
      · exact hi.2.2.2.2 3 (by decide)
      · exact hi.2.2.2.2 4 (by decide)
      · exact hi.2.2.2.2 5 (by decide)
      · exact hi.2.2.2.2 6 (by decide)
      · exact hi.2.2.2.2 7 (by decide)
      · exact hi.2.2.2.2 9 (by decide)
    · exact hi.2.2.2.2 10 (by decide)
  have hout : a.stacks 11 = [] := hi.2.2.2.2 11 (by decide)
  obtain ⟨b, ⟨n, hn, ht⟩, hb, hresult, houtput⟩ :=
    ExecClauseRelationScan.Preserving.program_runsIn .missingCore G H a ha hout
  let e := embedState regPort stackPort d b
  have he : Eval call n d e :=
    eval_call_from_state _ regPort stackPort d reg_injective stack_injective ht
  have hbstacks := local_stacks G H a b ha hb houtput
  have hestacks : e.stacks = Function.update d.stacks 11 [missing G H] := by
    change Function.extend stackPort b.stacks d.stacks = _
    rw [hbstacks, ProgramLinking.extend_update stack_injective]
    have hproject := congrArg StructuredProgram.State.stacks
      (embedState_project regPort stackPort d reg_injective stack_injective)
    change Function.extend stackPort a.stacks d.stacks = d.stacks at hproject
    rw [hproject]
    rfl
  refine ⟨n, hn, e, he, hestacks, ?_, ?_⟩
  · exact (embedState_register regPort stackPort d b reg_injective 14).trans hresult
  · exact embedState_register_frame _ _ _ _ _ (by decide)

abbrev command : Cmd 18 16 := .seq call (StackOps.clear 11 0 1)

theorem command_eval (G : Formula) (H : Clause) (width size : List Bool) (d : Data)
    (hi : Ready G H width size d) :
    ∃ n ≤ ExecClauseRelationScan.Preserving.bound G H + 5, ∃ e : Data,
      Eval command n d e ∧ Ready G H width size e ∧
      e.regs 14 = missing G H ∧ e.regs 17 = d.regs 17 := by
  obtain ⟨n, hn, e, he, hs, ha, hf⟩ := call_eval G H width size d hi
  let result := StackOps.cleared 11 0 1 e
  have hl : (e.stacks 11).length = 1 := by simp [hs]
  have hstacks : result.stacks = d.stacks := by
    have h11 : d.stacks 11 = [] := hi.2.2.2.2 11 (by decide)
    simp [result, StackOps.cleared, StackRoutines.clearStacks, hs, h11]
  refine ⟨n + (2 * (e.stacks 11).length + 3), by omega, result,
    Eval.seq he (StackOps.clear_eval 11 0 1 e), ?_, ?_, ?_⟩
  · simpa only [Ready, Clean, hstacks] using hi
  · simpa [result, StackOps.cleared, readRegs] using ha
  · simpa [result, StackOps.cleared, readRegs] using hf

end CoreCall

namespace SizeCall

def regPort (i : Fin 13) : Fin 18 := Fin.castAdd 5 i
def stackPort (i : Fin 9) : Fin 16 :=
  match i.val with
  | 0 => 13
  | 1 => 0
  | 2 => 1
  | 3 => 14
  | 4 => 15
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | _ => 5

theorem reg_injective : Function.Injective regPort := Fin.castAdd_injective 13 5
theorem stack_injective : Function.Injective stackPort := by decide

abbrev command : Cmd 18 16 := liftCommand FamilySizeGuardProgram.command 0 0 regPort stackPort

theorem command_eval (G : Formula) (H : Clause) (width size : List Bool) (d : Data)
    (hi : Ready G H width size d) :
    ∃ n ≤ FamilySizeGuardProgram.bound width size G, ∃ e : Data,
      Eval command n d e ∧ Ready G H width size e ∧
      e.regs 10 = FamilySizeGuardProgram.passes width size G ∧ e.regs 17 = d.regs 17 := by
  let a := projectState regPort stackPort d
  have h0 : a.stacks 0 = FamilySizeGuardProgram.familyCode G := hi.1
  have h3 : a.stacks 3 = width := hi.2.2.1
  have h4 : a.stacks 4 = size := hi.2.2.2.1
  have hw : FamilySizeGuardProgram.workEmpty a :=
    ⟨hi.2.2.2.2 0 (by decide), hi.2.2.2.2 1 (by decide),
      hi.2.2.2.2 2 (by decide), hi.2.2.2.2 3 (by decide),
      hi.2.2.2.2 4 (by decide), hi.2.2.2.2 5 (by decide)⟩
  obtain ⟨n, hn, b, he, hb0, hb3, hb4, hbw, hb10⟩ :=
    FamilySizeGuardProgram.command_eval width size G a h0 h3 h4 hw
  have hbs : b.stacks = a.stacks := by
    funext i
    rcases hw with ⟨ha1, ha2, ha5, ha6, ha7, ha8⟩
    rcases hbw with ⟨hb1, hb2, hb5, hb6, hb7, hb8⟩
    fin_cases i <;> simp_all
  let e := embedState regPort stackPort d b
  have hs : e.stacks = d.stacks := by
    change Function.extend stackPort b.stacks d.stacks = d.stacks
    rw [hbs]
    exact congrArg StructuredProgram.State.stacks
      (embedState_project regPort stackPort d reg_injective stack_injective)
  refine ⟨n + 1, hn, e, ?_, ?_, ?_, ?_⟩
  · exact eval_liftCommand_from_state FamilySizeGuardProgram.command 0 0
      regPort stackPort d reg_injective stack_injective he
  · simpa only [Ready, Clean, hs] using hi
  · exact (embedState_register regPort stackPort d b reg_injective 10).trans hb10
  · exact embedState_register_frame _ _ _ _ _ (by decide)

end SizeCall

theorem Ready.stacks_eq {G : Formula} {H : Clause} {width size : List Bool} {d e : Data}
    (hd : Ready G H width size d) (he : Ready G H width size e) : e.stacks = d.stacks := by
  funext i
  fin_cases i <;> first
  | exact he.1.trans hd.1.symm
  | exact he.2.1.trans hd.2.1.symm
  | exact he.2.2.1.trans hd.2.2.1.symm
  | exact he.2.2.2.1.trans hd.2.2.2.1.symm
  | exact (he.2.2.2.2 0 (by decide)).trans (hd.2.2.2.2 0 (by decide)).symm
  | exact (he.2.2.2.2 1 (by decide)).trans (hd.2.2.2.2 1 (by decide)).symm
  | exact (he.2.2.2.2 2 (by decide)).trans (hd.2.2.2.2 2 (by decide)).symm
  | exact (he.2.2.2.2 3 (by decide)).trans (hd.2.2.2.2 3 (by decide)).symm
  | exact (he.2.2.2.2 4 (by decide)).trans (hd.2.2.2.2 4 (by decide)).symm
  | exact (he.2.2.2.2 5 (by decide)).trans (hd.2.2.2.2 5 (by decide)).symm
  | exact (he.2.2.2.2 6 (by decide)).trans (hd.2.2.2.2 6 (by decide)).symm
  | exact (he.2.2.2.2 7 (by decide)).trans (hd.2.2.2.2 7 (by decide)).symm
  | exact (he.2.2.2.2 9 (by decide)).trans (hd.2.2.2.2 9 (by decide)).symm
  | exact (he.2.2.2.2 10 (by decide)).trans (hd.2.2.2.2 10 (by decide)).symm
  | exact (he.2.2.2.2 11 (by decide)).trans (hd.2.2.2.2 11 (by decide)).symm
  | exact (he.2.2.2.2 12 (by decide)).trans (hd.2.2.2.2 12 (by decide)).symm

def nonempty (H : Clause) : Bool := !H.isEmpty

def answer (G : Formula) (H : Clause) (width size : List Bool) : Bool :=
  ((FamilySizeGuardProgram.passes width size G && !CoreCall.missing G H) &&
    !ExecSunflowerPairScan.AllPairs.badPairs H G) && nonempty H

abbrev save : Cmd 18 16 := .base (.atom (.copy 17 10))
def saved (d : Data) : Data := (StructuredProgram.Atom.copy 17 10).eval d

abbrev foldCore : Cmd 18 16 :=
  .seq (.base (.atom (.bnot 16 14))) (.base (.atom (.band 17 17 16)))
def foldedCore (d : Data) : Data :=
  (StructuredProgram.Atom.band 17 17 16).eval ((StructuredProgram.Atom.bnot 16 14).eval d)

abbrev finish : Cmd 18 16 :=
  .seq (.base (.atom (.bnot 16 16))) (.seq (.base (.atom (.band 17 17 16)))
    (.seq (.base (.atom (.peek 8 16 0))) (.seq (.base (.atom (.band 17 17 16)))
      (.base (.atom (.push 12 17))))))
def finished (d : Data) : Data :=
  (StructuredProgram.Atom.push 12 17).eval
    ((StructuredProgram.Atom.band 17 17 16).eval
      ((StructuredProgram.Atom.peek 8 16 0).eval
        ((StructuredProgram.Atom.band 17 17 16).eval
          ((StructuredProgram.Atom.bnot 16 16).eval d))))

theorem save_eval (d : Data) : Eval save 1 d (saved d) := .base (.atom _ _)

theorem foldCore_eval (d : Data) : Eval foldCore 2 d (foldedCore d) :=
  .seq (.base (.atom _ _)) (.base (.atom _ _))

theorem finish_eval (d : Data) : Eval finish 5 d (finished d) :=
  .seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.seq (.base (.atom _ _))
    (.seq (.base (.atom _ _)) (.base (.atom _ _)))))

abbrev command : Cmd 18 16 :=
  .seq SizeCall.command (.seq save (.seq CoreCall.command
    (.seq foldCore (.seq PairCall.command finish))))

def bound (G : Formula) (H : Clause) (width size : List Bool) : ℕ :=
  FamilySizeGuardProgram.bound width size G + ExecClauseRelationScan.Preserving.bound G H +
    PairCall.bound G H + 13

def program := compiled command 13 12

theorem command_eval (G : Formula) (H : Clause) (width size : List Bool) (d : Data)
    (hi : Ready G H width size d) :
    ∃ n ≤ bound G H width size, ∃ e : Data, Eval command n d e ∧
      e.stacks = Function.update d.stacks 12 [answer G H width size] ∧
      e.regs 17 = answer G H width size := by
  obtain ⟨ns, hns, ds, hes, his, has, _⟩ := SizeCall.command_eval G H width size d hi
  have hisaved : Ready G H width size (saved ds) := his
  have hs17 : (saved ds).regs 17 = FamilySizeGuardProgram.passes width size G := by
    simpa [saved, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using has
  obtain ⟨nc, hnc, dc, hec, hic, hac, hfc⟩ := CoreCall.command_eval G H width size (saved ds) hisaved
  have hifold : Ready G H width size (foldedCore dc) := hic
  have hc17 : (foldedCore dc).regs 17 =
      (FamilySizeGuardProgram.passes width size G && !CoreCall.missing G H) := by
    simp [foldedCore, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
 StructuredProgram.State.ofCfg, execInstr,
      hfc, hs17, hac]
  obtain ⟨np, hnp, dp, hep, hip, hap, hfp⟩ := PairCall.command_eval G H width size (foldedCore dc) hifold
  have h17 : dp.regs 17 =
      (FamilySizeGuardProgram.passes width size G && !CoreCall.missing G H) := hfp.trans hc17
  have hH : dp.stacks 8 = Encoding.encodeList id H := hip.2.1
  have h12 : dp.stacks 12 = [] := hip.2.2.2.2 12 (by decide)
  have hhead : (Encoding.encodeList id H).head?.getD false = nonempty H := by
    cases H <;> rfl
  have hfinish17 : (finished dp).regs 17 = answer G H width size := by
    simp [finished, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
 StructuredProgram.State.ofCfg, execInstr,
      readRegs, h17, hap, hH, hhead, answer]
  have hfinishS : (finished dp).stacks =
      Function.update dp.stacks 12 [answer G H width size] := by
    simp [finished, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
 StructuredProgram.State.ofCfg, execInstr,
      readRegs, h17, hap, hH, hhead, h12, answer]
  refine ⟨ns + (1 + (nc + (2 + (np + 5)))), ?_, finished dp, ?_, ?_, hfinish17⟩
  · unfold bound
    omega
  · exact Eval.seq hes (Eval.seq (save_eval ds) (Eval.seq hec
      (Eval.seq (foldCore_eval dc) (Eval.seq hep (finish_eval dp)))))
  · simpa only [Ready.stacks_eq hi hip] using hfinishS

/-- One finite instruction table decides the concrete candidate checks.
Literal and clause distinctness are supplied separately by normalization and
the increasing-index selector; the raw checks do not assume those facts. -/
theorem program_run (G : Formula) (H : Clause) (width size : List Bool) (d : Data)
    (hi : Ready G H width size d) :
    ∃ e : Data, RunsIn program (bound G H width size + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 12 [answer G H width size] ∧
      e.regs 17 = answer G H width size := by
  obtain ⟨n, hn, e, he, hs, ha⟩ := command_eval G H width size d hi
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 13 12⟩, hs, ha⟩

theorem primitive_run (G : Formula) (H : Clause) (width size : List Bool) (d : Data)
    (hi : Ready G H width size d) :
    ∃ e : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (bound G H width size + 1))
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) ∧
      e.stacks = Function.update d.stacks 12 [answer G H width size] ∧
      e.regs 17 = answer G H width size := by
  obtain ⟨e, ht, hs, ha⟩ := program_run G H width size d hi
  exact ⟨e, BitProgram.primitive_execution program ht, hs, ha⟩

theorem core_false_iff (G : Formula) (H : Clause) :
    CoreCall.missing G H = false ↔ ∀ C ∈ G, ExecCNF.subset H C = true := by
  simp [CoreCall.missing, ExecClauseRelationScan.test, List.any_eq_false]

theorem answer_true_iff (G : Formula) (H : Clause) (width size : List Bool) :
    answer G H width size = true ↔
      (((G.length = BinaryArithmetic.toNat size ∧
        ∀ C ∈ G, C.length = BinaryArithmetic.toNat width) ∧
        (∀ C ∈ G, ExecCNF.subset H C = true)) ∧
        G.Pairwise (fun C D => SubexpSunflowerProgram.Intersection.ContainsIntersection C D H)) ∧
        H ≠ [] := by
  simp [answer, FamilySizeGuardProgram.passes_iff, core_false_iff,
    ExecSunflowerPairScan.AllPairs.no_badPairs_iff, nonempty]

end SubexponentialSAT.ExecSunflowerCandidateProgram

end OAI.Algorithms
