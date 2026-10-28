import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFSubset
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! A concrete scope-membership subroutine for incidence-plan preparation.
The reversed scope record occupies stack 8 and the reversed query stack 2.
Stacks 0,1,3,4 are empty work ports; all remaining stacks are framed.
-/
namespace SubexponentialSAT.SubexpScopeMembershipProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 10 10

def stackMap : Fin 8 → Fin 10 := ![5, 2, 6, 0, 1, 3, 4, 7]

theorem stackMap_injective : Function.Injective stackMap := by decide

def restrict (d : Data) : ExecCNFSubset.Data := ⟨d.regs, d.stacks ∘ stackMap⟩

theorem embed_restrict (d : Data) : embedState id stackMap d (restrict d) = d := by
  apply embedState_eq_of_ports id stackMap d d (restrict d)
    Function.injective_id stackMap_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; rfl
  · intros; rfl

abbrev member : Cmd 10 10 :=
  .call (ProgramLinking.liftProgram
    (StructuredCalls.compiled ExecCNFSubset.memberCall 3 4) id stackMap)

theorem member_eval (query : List Bool) (records : List (List Bool)) (d : Data)
    (h0 : d.stacks 0 = Encoding.encodeList id records)
    (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = query.reverse)
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ (n : ℕ) (e : Data),
      Eval member n d e ∧
      n ≤ (20 * query.length + 30) * (Encoding.encodeList id records).length + 3 ∧
      e.regs 4 = decide (query ∈ records) ∧
      (e.stacks 0).length ≤ (Encoding.encodeList id records).length ∧
      e.stacks 1 = [decide (query ∈ records)] ∧ e.stacks 2 = d.stacks 2 ∧
      e.stacks 3 = [] ∧ e.stacks 4 = [] ∧
      (∀ i : Fin 10, 5 ≤ i.val → e.stacks i = d.stacks i) ∧
      (∀ i : Fin 10, 7 ≤ i.val → e.regs i = d.regs i) := by
  obtain ⟨n, hn, b, he, hflag, hsource, hout, hquery, hcopy, htmp,
      hframe0, hframe2, hframe7, hreg7, hreg8, hreg9⟩ :=
    ExecCNFSubset.memberCall_eval query records (restrict d) h0 h2 h1 h3 h4
  have ht := StructuredCalls.compiled_halt_trace he 3 4
  have hl := eval_call_lifted (StructuredCalls.compiled ExecCNFSubset.memberCall 3 4)
    id stackMap d Function.injective_id stackMap_injective ht
  rw [embed_restrict] at hl
  let e := embedState id stackMap d b
  have hstack (i : Fin 8) : e.stacks (stackMap i) = b.stacks i :=
    embedState_stack id stackMap d b stackMap_injective i
  have hreg (i : Fin 10) : e.regs i = b.regs i :=
    embedState_register id stackMap d b Function.injective_id i
  refine ⟨n + 1, e, hl, by omega, (hreg 4).trans hflag, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← show stackMap (3 : Fin 8) = 0 by decide, hstack 3]
    exact hsource
  · exact (hstack 4).trans hout
  · exact (hstack 1).trans (hquery.trans h2.symm)
  · exact (hstack 5).trans hcopy
  · exact (hstack 6).trans htmp
  · intro i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · exact (hstack 0).trans hframe0
    · exact (hstack 2).trans hframe2
    · exact (hstack 7).trans hframe7
    · exact embedState_stack_frame id stackMap d b 8 (by decide)
    · exact embedState_stack_frame id stackMap d b 9 (by decide)
  · intro i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · simp at hi
    · exact (hreg 7).trans hreg7
    · exact (hreg 8).trans hreg8
    · exact (hreg 9).trans hreg9

abbrev transfer : Cmd 10 10 := .call (StackRoutines.transferProgram 8 0 0 1)

def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 8 0 d.stacks⟩

theorem transfer_eval (d : Data) :
    Eval transfer (3 * (d.stacks 8).length + 3) d (transferred d) :=
  .call _ (ListRegisterProgram.transfer_run 8 0 0 1 (by decide) (by decide) d.regs d.stacks)

abbrev clear (i : Fin 10) : Cmd 10 10 := .call (StackRoutines.clearProgram i 0 1)

def cleared (i : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks i []⟩

theorem clear_eval (i : Fin 10) (d : Data) :
    Eval (clear i) (2 * (d.stacks i).length + 3) d (cleared i d) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 d.regs d.stacks)

abbrev command : Cmd 10 10 := .seq transfer (.seq member (.seq (clear 0) (clear 1)))

private theorem cost_bound {q L x n : ℕ}
    (hn : n ≤ (20 * q + 30) * L + 3) (hx : x ≤ L) :
    (3 * L + 3) + (n + ((2 * x + 3) + 5)) ≤ 128 * (q + 1) * (L + 1) := by
  nlinarith

/-- The only changed stack is the consumed payload on 8. Membership comes
from the actual encoded comparator and iterator, and outer loop registers survive. -/
theorem command_eval (query : List Bool) (records : List (List Bool)) (d : Data)
    (hp : d.stacks 8 = (Encoding.encodeList id records).reverse)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = query.reverse) (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval command n d ⟨rf, Function.update d.stacks 8 []⟩ ∧
      rf 4 = decide (query ∈ records) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = d.regs i) ∧
      n ≤ 128 * (query.length + 1) * ((Encoding.encodeList id records).length + 1) := by
  have hs0 : (transferred d).stacks 0 = Encoding.encodeList id records := by
    simp [transferred, StackRoutines.transferStacks, hp, h0]
  obtain ⟨n, e, he, hn, hf, hs, ho, hq, hc, ht, hframe, hregs⟩ :=
    member_eval query records (transferred d) hs0
      (by simpa [transferred, StackRoutines.transferStacks] using h1)
      (by simpa [transferred, StackRoutines.transferStacks] using h2)
      (by simpa [transferred, StackRoutines.transferStacks] using h3)
      (by simpa [transferred, StackRoutines.transferStacks] using h4)
  let e1 := cleared 0 e
  let e2 := cleared 1 e1
  have ho' : e1.stacks 1 = [decide (query ∈ records)] := by simpa [e1, cleared] using ho
  have hclear1 : Eval (clear 1) 5 e1 e2 := by
    simpa only [ho', List.length_cons, List.length_nil] using clear_eval 1 e1
  have hend : e2 = (⟨e2.regs, Function.update d.stacks 8 []⟩ : Data) := by
    apply congrArg (StructuredProgram.State.mk e2.regs)
    funext i
    fin_cases i
    · simp [ e1, cleared, h0]
    · simp [ e1, cleared, h1]
    · simp [ e1, cleared, hq, transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hc, h3]
    · simp [ e1, cleared, ht, h4]
    · simp [ e1, cleared, hframe 5 (by decide), transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hframe 6 (by decide), transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hframe 7 (by decide), transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hframe 8 (by decide), transferred, StackRoutines.transferStacks]
    · simp [ e1, cleared, hframe 9 (by decide), transferred, StackRoutines.transferStacks]
  have hexec := (transfer_eval d).seq (he.seq ((clear_eval 0 e).seq hclear1))
  rw [hend] at hexec
  refine ⟨(3 * (d.stacks 8).length + 3) + (n + ((2 * (e.stacks 0).length + 3) + 5)),
    e2.regs, hexec, ?_, ?_, ?_⟩
  · simpa [e2, e1, cleared, readRegs] using hf
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; contradiction
    have hi1 : i ≠ 1 := by intro h; subst i; contradiction
    simpa [e2, e1, cleared, readRegs, transferred, hi0, hi1] using hregs i hi
  · rw [hp, List.length_reverse]
    exact cost_bound hn hs

theorem encodeNat_mem (v : ℕ) (scope : List ℕ) :
    Encoding.encodeNat v ∈ scope.map Encoding.encodeNat ↔ v ∈ scope := by
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := List.mem_map.mp h
    exact Encoding.encodeNat_injective he ▸ hx
  · intro h
    exact List.mem_map.mpr ⟨v, h, rfl⟩

theorem scope_eval (v : ℕ) (scope : List ℕ) (d : Data)
    (hp : d.stacks 8 = (Encoding.encodeList Encoding.encodeNat scope).reverse)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = (Encoding.encodeNat v).reverse)
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval command n d ⟨rf, Function.update d.stacks 8 []⟩ ∧
      rf 4 = decide (v ∈ scope) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = d.regs i) ∧
      n ≤ 128 * (v + 2) * ((Encoding.encodeList Encoding.encodeNat scope).length + 1) := by
  obtain ⟨n, rf, he, hf, hr, hn⟩ := command_eval (Encoding.encodeNat v)
    (scope.map Encoding.encodeNat) d
      (by simpa only [ExecCNFMembership.encodeList_map_encodeNat] using hp) h0 h1 h2 h3 h4
  refine ⟨n, rf, he, ?_, hr, ?_⟩
  · simpa only [encodeNat_mem] using hf
  · simpa only [Encoding.length_encodeNat, ExecCNFMembership.encodeList_map_encodeNat,
      Nat.add_assoc] using hn

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
