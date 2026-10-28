import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticDivisorContracts

namespace OAI.Algorithms

/-! # Measured universal scans of the generated quartic divisor tables -/

namespace SubexponentialSAT.SubexpQuarticDivisorScans

open BitProgram StructuredCalls SubexpQuarticProducerControl
open SubexpQuarticScanInvariant SubexpQuarticDivisorContracts
open Subexp.BlockSearchProgram
open SubexpTupleRefinement

theorem frame_refl (d : Data) : OuterFrame d d :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem frame_trans {a b c : Data} (hab : OuterFrame a b) (hbc : OuterFrame b c) :
    OuterFrame a c :=
  ⟨fun j hj => (hbc.1 j hj).trans (hab.1 j hj),
    fun j hj => (hbc.2 j hj).trans (hab.2 j hj)⟩

theorem framed_all_eval (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p)
    (ports : SavedPorts 14 35) (hports : ports.toPorts = innerPorts)
    (callback : Command) (test : List Bool → Bool) (cost : ℕ)
    (records : List (List Bool)) (width : ℕ)
    (hwidth : ∀ bits ∈ records, bits.length = width)
    (contract : RecordPrograms.CallbackContractWithOn innerPorts callback test
      (fun _ => cost) (Ready p M c) (fun _ a b => OuterFrame a b)
      (fun bits => bits ∈ records))
    (base : Data) (hb : Ready p M c base)
    (hsaved : base.stacks ports.saved = ProgramEncoding.encodeRecords records)
    (htemp : base.stacks ports.temporary = [])
    (h23 : base.stacks 23 = []) (h24 : base.stacks 24 = []) :
    ∃ n next,
      n ≤ records.length * (cost + 24 * width + 27) + 23 ∧
      Eval (savedAllCommand ports callback) n base next ∧
      Ready p M c next ∧ OuterFrame base next ∧
      next.stacks 23 = [] ∧ next.stacks 24 = [] ∧ next.regs 10 = records.all test := by
  let invariant := fun d => Ready p M c d ∧ OuterFrame base d
  have hc : RecordPrograms.CallbackContractOn ports.toPorts callback test
      (fun _ => cost) invariant (fun bits => bits ∈ records) := by
    intro bits tail a hbits ha
    obtain ⟨n, b, hn, hb, hf, he⟩ := contract bits tail a hbits ha.1
    refine ⟨n, b, hn, ⟨hb, frame_trans ha.2 hf⟩, ?_⟩
    simpa only [hports] using he
  obtain ⟨n, b, hn, hb', he⟩ := savedAllCommand_eval ports callback test
    (fun _ => cost) invariant (fun bits => bits ∈ records) hc records base
    (fun _ h => h) ⟨hb, frame_refl base⟩ hsaved htemp
    (base.regs 8) (base.regs 9) (base.regs 10)
  rw [hports] at he
  have hstart : RecordPrograms.state innerPorts base (base.regs 8) (base.regs 9)
      (base.regs 10) [] [] = base :=
    RecordPrograms.state_eq_self innerPorts base _ _ _ [] [] rfl rfl rfl h23 h24
  rw [hstart] at he
  let next := RecordPrograms.state innerPorts b false true (records.all test) [] []
  have hframe : OuterFrame base next := by
    constructor
    · intro j hj
      have hjs : j ≠ 23 := by intro h; have := congrArg Fin.val h; omega
      have hjp : j ≠ 24 := by intro h; have := congrArg Fin.val h; omega
      exact (inner_state_stack b false true (records.all test) [] [] j hjs hjp).trans (hb'.2.1 j hj)
    · intro j hj
      have h8 : j ≠ 8 := by intro h; have := congrArg Fin.val h; omega
      have h9 : j ≠ 9 := by intro h; have := congrArg Fin.val h; omega
      have h10 : j ≠ 10 := by intro h; have := congrArg Fin.val h; omega
      exact (RecordPrograms.state_register_frame innerPorts b false true (records.all test)
        [] [] j h8 h9 h10).trans (hb'.2.2 j hj)
  have hlen := ProgramEncoding.encodeRecords_length_le records width
    (fun bits hbits => (hwidth bits hbits).le)
  have hbudget := SubexpQuarticSelector.uniform_budget records width (cost + 2) hwidth
  have hcost : n ≤ records.length * (cost + 24 * width + 27) + 23 := by
    rw [hbudget] at hn
    calc
      n ≤ 9 * (ProgramEncoding.encodeRecords records).length +
          records.length * (6 * width + (cost + 2) + 7) + 14 := hn
      _ ≤ 9 * (1 + (2 * width + 2) * records.length) +
          records.length * (6 * width + (cost + 2) + 7) + 14 := by omega
      _ = records.length * (cost + 24 * width + 27) + 23 := by ring
  refine ⟨n, next, hcost, he,
    ready_inner_state p M c b hb'.1 false true (records.all test) [] [], hframe, ?_, ?_, ?_⟩
  · exact RecordPrograms.state_source innerPorts b false true (records.all test) [] []
  · exact RecordPrograms.state_payload innerPorts b false true (records.all test) [] []
  · exact RecordPrograms.state_found innerPorts b false true (records.all test) [] []

theorem linear_scan (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p)
    (base : Data) (hb : Ready p M c base)
    (hsaved : base.stacks 25 = ProgramEncoding.encodeRecords (linearRecords p))
    (h27 : base.stacks 27 = []) (h23 : base.stacks 23 = []) (h24 : base.stacks 24 = []) :
    ∃ n next,
      n ≤ p * (51000 * (SubexpLiftRing.baseWidth p 1 + 1)^2 +
        24 * SubexpEnumerationPayload.scalarWidth p + 27) + 23 ∧
      Eval (savedAllCommand linearPorts linearCallback) n base next ∧
      Ready p M c next ∧ OuterFrame base next ∧ next.stacks 23 = [] ∧ next.stacks 24 = [] ∧
      next.regs 10 = (QuarticSearch.elements p).all (QuarticSearch.linearPass p c) := by
  have hw : ∀ bits ∈ linearRecords p, bits.length = SubexpEnumerationPayload.scalarWidth p := by
    intro bits hbits
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hbits
    exact (SubexpEnumerationPayload.scalarCode p).length_block a
  obtain ⟨n, next, hn, he, hr, hf, h23', h24', hflag⟩ := framed_all_eval p M c linearPorts rfl
    linearCallback (SubexpQuarticByteSpec.linearTest p c)
    (51000 * (SubexpLiftRing.baseWidth p 1 + 1)^2) (linearRecords p)
    (SubexpEnumerationPayload.scalarWidth p) hw (linear_contract p M c) base hb hsaved h27 h23 h24
  refine ⟨n, next, ?_, he, hr, hf, h23', h24', ?_⟩
  · simpa [linearRecords] using hn
  · simpa only [linearRecords, SubexpQuarticByteSpec.all_linear] using hflag

theorem quadratic_scan (p : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p 1) (c : Fin 4 → ZMod p)
    (base : Data) (hb : Ready p M c base)
    (hsaved : base.stacks 26 = ProgramEncoding.encodeRecords (quadraticRecords p))
    (h27 : base.stacks 27 = []) (h23 : base.stacks 23 = []) (h24 : base.stacks 24 = []) :
    ∃ n next,
      n ≤ p^2 * (76000 * (SubexpLiftRing.baseWidth p 1 + 1)^2 +
        48 * SubexpEnumerationPayload.scalarWidth p + 27) + 23 ∧
      Eval (savedAllCommand quadraticPorts quadraticCallback) n base next ∧
      Ready p M c next ∧ OuterFrame base next ∧ next.stacks 23 = [] ∧ next.stacks 24 = [] ∧
      next.regs 10 = (QuarticSearch.vectors (QuarticSearch.elements p) 2).all
        (QuarticSearch.quadraticPass p c) := by
  have hw : ∀ bits ∈ quadraticRecords p,
      bits.length = 2 * SubexpEnumerationPayload.scalarWidth p := by
    intro bits hbits
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hbits
    simp [encodeTuple, SubexpEnumerationPayload.scalarCode]
    omega
  obtain ⟨n, next, hn, he, hr, hf, h23', h24', hflag⟩ := framed_all_eval p M c quadraticPorts rfl
    quadraticCallback (SubexpQuarticByteSpec.quadraticTest p c)
    (76000 * (SubexpLiftRing.baseWidth p 1 + 1)^2) (quadraticRecords p)
    (2 * SubexpEnumerationPayload.scalarWidth p) hw (quadratic_contract p M c) base hb hsaved h27 h23 h24
  refine ⟨n, next, ?_, he, hr, hf, h23', h24', ?_⟩
  · simpa [quadraticRecords, QuarticSearch.length_vectors,
      show 24 * (2 * SubexpEnumerationPayload.scalarWidth p) =
        48 * SubexpEnumerationPayload.scalarWidth p by omega] using hn
  · simpa only [quadraticRecords, SubexpQuarticByteSpec.all_quadratic] using hflag

end SubexponentialSAT.SubexpQuarticDivisorScans

end OAI.Algorithms
