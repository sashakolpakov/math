import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticScanInvariant

namespace OAI.Algorithms

/-! # Actual divisor callbacks satisfy the framed-list scan contracts -/

namespace SubexponentialSAT.SubexpQuarticDivisorContracts

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpQuarticProducerControl SubexpQuarticCallback SubexpQuarticScanInvariant
open SubexpEnumerationPayload SubexpTupleRefinement

def OuterFrame (before after : Data) : Prop :=
  (∀ j : Fin 35, 25 ≤ j.val → after.stacks j = before.stacks j) ∧
  (∀ j : Fin 14, 11 ≤ j.val → after.regs j = before.regs j)

def linearRecords (p : ℕ) [Fact p.Prime] : List (List Bool) :=
  (QuarticSearch.elements p).map (scalarCode p).block

def quadraticRecords (p : ℕ) [Fact p.Prime] : List (List Bool) :=
  (QuarticSearch.vectors (QuarticSearch.elements p) 2).map (encodeTuple (scalarCode p))

theorem outerFrame_of_callback (base next : Data) (tail bits : List Bool)
    (hbase30 : base.stacks 30 = []) (hnext30 : next.stacks 30 = [])
    (hstacks : ∀ j : Fin 35, 23 ≤ j.val → j ≠ 24 → j ≠ 30 →
      next.stacks j = (RecordPrograms.state innerPorts base false true false tail bits.reverse).stacks j)
    (hregs : ∀ j : Fin 14, 11 ≤ j.val →
      next.regs j = (RecordPrograms.state innerPorts base false true false tail bits.reverse).regs j) :
    OuterFrame base next := by
  constructor
  · intro j hj
    by_cases h30 : j = 30
    · subst j
      exact hnext30.trans hbase30.symm
    · have h23 : j ≠ 23 := by intro h; have := congrArg Fin.val h; omega
      have h24 : j ≠ 24 := by intro h; have := congrArg Fin.val h; omega
      exact (hstacks j (by omega) h24 h30).trans
        (inner_state_stack base false true false tail bits.reverse j h23 h24)
  · intro j hj
    have h8 : j ≠ 8 := by intro h; have := congrArg Fin.val h; omega
    have h9 : j ≠ 9 := by intro h; have := congrArg Fin.val h; omega
    have h10 : j ≠ 10 := by intro h; have := congrArg Fin.val h; omega
    exact (hregs j hj).trans (RecordPrograms.state_register_frame innerPorts base false true false
      tail bits.reverse j h8 h9 h10)

theorem exit_state_eq (base next : Data) (tail bits : List Bool) (flag : Bool)
    (h8 : next.regs 8 = false) (h9 : next.regs 9 = true) (h10 : next.regs 10 = flag)
    (h24 : next.stacks 24 = [])
    (hstack : ∀ j : Fin 35, 23 ≤ j.val → j ≠ 24 → j ≠ 30 →
      next.stacks j = (RecordPrograms.state innerPorts base false true false tail bits.reverse).stacks j) :
    RecordPrograms.state innerPorts next false true flag tail [] = next := by
  have h23 : next.stacks 23 = tail := by
    exact (hstack 23 (by decide) (by decide) (by decide)).trans
      (RecordPrograms.state_source innerPorts base false true false tail bits.reverse)
  exact RecordPrograms.state_eq_self innerPorts next false true flag tail [] h8 h9 h10 h23 h24

theorem linear_contract (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p) :
    RecordPrograms.CallbackContractWithOn innerPorts linearCallback
      (SubexpQuarticByteSpec.linearTest p c)
      (fun _ => 51000 * (baseWidth p 1 + 1)^2) (Ready p M c)
      (fun _ a b => OuterFrame a b) (fun bits => bits ∈ linearRecords p) := by
  intro bits tail base hbits hbase
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hbits
  let bits := (scalarCode p).block a
  let start := RecordPrograms.state innerPorts base false true false tail bits.reverse
  have hstart : Ready p M c start := ready_inner_state p M c base hbase false true false tail bits.reverse
  obtain ⟨bank, hb, hm, hc, h30, h32, h31⟩ := hstart
  have hminus : wordValue p 1 (bank 6) = -1 := by
    unfold wordValue
    rw [Nat.pow_one]
    exact hm
  have hin : start.stacks 24 = (sourceWord p a).val.reverse := by
    have hin' : start.stacks 24 = bits.reverse :=
      RecordPrograms.state_payload innerPorts base false true false tail bits.reverse
    simpa only [bits, sourceWord] using hin'
  obtain ⟨n, next, nextBank, hn, he, hrep, h8, h9, h10, h24, hn30, hkeep, hsf, hrf⟩ :=
    linear_callback_eval p 1 M start bank hb hminus (sourceWord p a) hin h30 h32 h31
  have hflagBase : next.regs 10 = QuarticSearch.linearPass p
      (fun i => baseValue p (![bank 0, bank 1, bank 2, bank 3] i))
      (baseValue p (sourceWord p a)) := by
    have h := h10
    unfold wordValue at h
    rw [Nat.pow_one] at h
    exact h
  rw [← coefficientValue_eq_vector, hc, sourceWord_value] at hflagBase
  have hflag : next.regs 10 = SubexpQuarticByteSpec.linearTest p c bits := by
    simpa only [bits, SubexpQuarticByteSpec.linearTest_block] using hflagBase
  have hnextReady : Ready p M c next :=
    ready_of_transition p M c start next ⟨bank, hb, hm, hc, h30, h32, h31⟩
      nextBank hrep (fun i h4 _ => hkeep i h4)
      hn30 (hsf 32 (by decide) (by decide) (by decide))
      (hsf 31 (by decide) (by decide) (by decide))
  have hbase30 : base.stacks 30 = [] := by
    obtain ⟨_, _, _, _, h, _, _⟩ := hbase
    exact h
  have hframe : OuterFrame base next :=
    outerFrame_of_callback base next tail bits hbase30 hn30 hsf hrf
  have hend := exit_state_eq base next tail bits (SubexpQuarticByteSpec.linearTest p c bits)
    h8 h9 hflag h24 hsf
  refine ⟨n, next, hn, hnextReady, hframe, ?_⟩
  change Eval linearCallback n start
    (RecordPrograms.state innerPorts next false true (SubexpQuarticByteSpec.linearTest p c bits) tail [])
  rw [hend]
  exact he

theorem quadratic_contract (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p) :
    RecordPrograms.CallbackContractWithOn innerPorts quadraticCallback
      (SubexpQuarticByteSpec.quadraticTest p c)
      (fun _ => 76000 * (baseWidth p 1 + 1)^2) (Ready p M c)
      (fun _ a b => OuterFrame a b) (fun bits => bits ∈ quadraticRecords p) := by
  intro bits tail base hbits hbase
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hbits
  let bits := encodeTuple (scalarCode p) a
  let start := RecordPrograms.state innerPorts base false true false tail bits.reverse
  have hstart : Ready p M c start := ready_inner_state p M c base hbase false true false tail bits.reverse
  obtain ⟨bank, hb, hm, hc, h30, h32, h31⟩ := hstart
  have hminus : wordValue p 1 (bank 6) = -1 := by
    unfold wordValue
    rw [Nat.pow_one]
    exact hm
  have hin : start.stacks 24 =
      ((sourceWord p (a 0)).val ++ (sourceWord p (a 1)).val).reverse := by
    have hin' : start.stacks 24 = bits.reverse :=
      RecordPrograms.state_payload innerPorts base false true false tail bits.reverse
    simpa [bits, sourceWord, encodeTuple, List.ofFn_succ,
      StackEncoding.encodeDataStack] using hin'
  obtain ⟨n, next, nextBank, hn, he, hrep, h8, h9, h10, h24, hn30, hkeep, hsf, hrf⟩ :=
    quadratic_callback_eval p 1 M start bank hb hminus
      (sourceWord p (a 0)) (sourceWord p (a 1)) hin h30 h32 h31
  have hflagBase : next.regs 10 = QuarticSearch.quadraticPass p
      (fun i => baseValue p (![bank 0, bank 1, bank 2, bank 3] i))
      ![baseValue p (sourceWord p (a 0)), baseValue p (sourceWord p (a 1))] := by
    have h := h10
    unfold wordValue at h
    rw [Nat.pow_one] at h
    exact h
  have ha' : (![a 0, a 1] : Fin 2 → ZMod p) = a := by
    funext i
    fin_cases i <;> rfl
  rw [← coefficientValue_eq_vector, hc, sourceWord_value, sourceWord_value, ha'] at hflagBase
  have hflag : next.regs 10 = SubexpQuarticByteSpec.quadraticTest p c bits := by
    simpa only [bits, SubexpQuarticByteSpec.quadraticTest_block] using hflagBase
  have hnextReady : Ready p M c next :=
    ready_of_transition p M c start next ⟨bank, hb, hm, hc, h30, h32, h31⟩
      nextBank hrep hkeep hn30 (hsf 32 (by decide) (by decide) (by decide))
      (hsf 31 (by decide) (by decide) (by decide))
  have hbase30 : base.stacks 30 = [] := by
    obtain ⟨_, _, _, _, h, _, _⟩ := hbase
    exact h
  have hframe : OuterFrame base next :=
    outerFrame_of_callback base next tail bits hbase30 hn30 hsf hrf
  have hend := exit_state_eq base next tail bits (SubexpQuarticByteSpec.quadraticTest p c bits)
    h8 h9 hflag h24 hsf
  refine ⟨n, next, hn, hnextReady, hframe, ?_⟩
  change Eval quadraticCallback n start
    (RecordPrograms.state innerPorts next false true (SubexpQuarticByteSpec.quadraticTest p c bits) tail [])
  rw [hend]
  exact he

end SubexponentialSAT.SubexpQuarticDivisorContracts

end OAI.Algorithms
