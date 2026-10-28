import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgramInputs
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreBounds

namespace OAI.Algorithms

/-! Actual depth-two tuple program builds all raw incidence-pair records.
Its input has one two-address record per incidence, not a quadratic table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp

def planAlphabet (plans : List (List ℕ)) : List (List Bool) :=
  plans.map (fun p => Encoding.frame (CollisionStreamProgram.planBytes p))

def generatedRawPairs (plans : List (List ℕ)) : List PlanPair :=
  (TupleProgram.powerRows (planAlphabet plans) 2 [[]]).map PairScoreProgram.readPair

theorem generatedRawPairs_perm (plans : List (List ℕ)) :
    (generatedRawPairs plans).Perm (plans.product plans) :=
  CandidateScoreRefinement.generated_pair_payloads_decode plans

theorem generatedRawPairs_length (plans : List (List ℕ)) :
    (generatedRawPairs plans).length = plans.length^2 := by
  exact (generatedRawPairs_perm plans).length_eq.trans
    ((List.length_product plans plans).trans (pow_two _).symm)

theorem generatedRawPairs_bytes (plans : List (List ℕ)) :
    ProgramEncoding.encodeRecords (TupleProgram.powerRows (planAlphabet plans) 2 [[]]) =
      PairScoreProgram.pairRecords (generatedRawPairs plans) := by
  apply congrArg ProgramEncoding.encodeRecords
  unfold generatedRawPairs
  rw [List.map_map]
  let rows := TupleProgram.powerRows (planAlphabet plans) 2 [[]]
  change rows = rows.map (fun x => PairScoreProgram.pairBytes (PairScoreProgram.readPair x))
  calc
    rows = rows.map id := (List.map_id _).symm
    _ = _ := by
      apply List.map_congr_left
      intro row hrow
      have hh := (CandidateScoreRefinement.generated_pair_payloads plans).mem_iff.mp hrow
      obtain ⟨pair, _, rfl⟩ := List.mem_map.mp hh
      simp

def pairInput (plans : List (List ℕ)) : SubexponentialSAT.StructuredProgram.State 10 9 :=
  ⟨fun _ => false, fun j =>
    if j = 1 then ProgramEncoding.encodeRecords (planAlphabet plans)
    else if j = 8 then [true, true] else []⟩

theorem pairInput_ready (plans : List (List ℕ)) :
    TupleProgram.outerInvariant (planAlphabet plans) [true,true] false (pairInput plans) := by
  simp [TupleProgram.outerInvariant, pairInput]

/-- The fixed 83-instruction tuple generator produces the quadratic raw table. -/
theorem rawPairProgram_runsIn (plans : List (List ℕ)) :
    ∃ e : SubexponentialSAT.StructuredProgram.State 10 9,
      RunsIn TupleProgram.generateProgram
        (TupleProgram.powerCost (planAlphabet plans) 2 [[]] + 9)
        ((pairInput plans).withPC (some TupleProgram.generateProgram.entry)) (e.withPC none) ∧
      e.stacks 0 = PairScoreProgram.pairRecords (generatedRawPairs plans) := by
  obtain ⟨e, he, hr⟩ := TupleProgram.generateProgram_runsIn
    (planAlphabet plans) [true,true] false (pairInput plans) (pairInput_ready plans)
    (by simp [pairInput]) (by simp [pairInput]) (by simp [pairInput])
  refine ⟨e, hr, ?_⟩
  exact he.2.1.trans (generatedRawPairs_bytes plans)

theorem rawPairProgram_primitive (plans : List (List ℕ)) :
    ∃ e : SubexponentialSAT.StructuredProgram.State 10 9,
      SubexponentialSAT.Computation.RunsIn (primitive TupleProgram.generateProgram).step
        (primitiveOverhead TupleProgram.generateProgram *
          (TupleProgram.powerCost (planAlphabet plans) 2 [[]] + 9))
        (primitiveCfg TupleProgram.generateProgram
          ((pairInput plans).withPC (some TupleProgram.generateProgram.entry)))
        (primitiveCfg TupleProgram.generateProgram (e.withPC none)) ∧
      e.stacks 0 = PairScoreProgram.pairRecords (generatedRawPairs plans) := by
  obtain ⟨e, hr, he⟩ := rawPairProgram_runsIn plans
  exact ⟨e, primitive_execution TupleProgram.generateProgram hr, he⟩

theorem planAlphabet_width (M : ℕ) (plans : List (List ℕ))
    (hlen : ∀ p ∈ plans, p.length ≤ 2) (hindex : ∀ p ∈ plans, ∀ i ∈ p, i < M) :
    ∀ row ∈ planAlphabet plans, row.length ≤ 8*M+11 := by
  intro row hrow
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrow
  have h := PairPreparationBounds.planBytes_le p M (fun i hi => (hindex p hp i hi).le)
  have hlen' := hlen p hp
  simp only [Encoding.length_frame]
  nlinarith

theorem rawPairProgram_cost (M : ℕ) (plans : List (List ℕ)) (hne : plans ≠ [])
    (hlen : ∀ p ∈ plans, p.length ≤ 2) (hindex : ∀ p ∈ plans, ∀ i ∈ p, i < M) :
    TupleProgram.powerCost (planAlphabet plans) 2 [[]] + 9 ≤
      2400 * plans.length^2 * (24*M+34) + 9 := by
  have hq : 1 ≤ (planAlphabet plans).length := by
    have hpos : 0 < (planAlphabet plans).length := by
      simpa only [planAlphabet, List.length_map] using List.length_pos_iff.mpr hne
    omega
  have h := PairScoreBounds.generated_powerCost_le (planAlphabet plans) 2 (8*M+11)
    hq (planAlphabet_width M plans hlen hindex)
  calc
    _ ≤ 800*(2+1)*(planAlphabet plans).length^2*((2+1)*(8*M+11)+1)+9 :=
      Nat.add_le_add_right h 9
    _ = _ := by simp only [planAlphabet, List.length_map]; ring

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
