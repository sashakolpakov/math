import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticProducer

namespace OAI.Algorithms

/-! # A fixed-degree bound for the concrete quartic coefficient producer -/

namespace SubexponentialSAT.SubexpQuarticProducerBounds

open SubexpQuarticProducer SubexpQuarticCandidateContract SubexpQuarticStorageBounds

/-- The nonnegative coefficient expansion avoids any parameter-dependent
constant in the producer's polynomial running-time bound. -/
private def slack (p b : ℕ) : ℕ :=
  (200000*b^2 + 397748*b + 197408) +
  p * (1200000*b^2 + 2391804*b + 1191804) +
  p^2 * (3000000*b^2 + 5987728*b + 2987864) +
  p^3 * (4000000*b^2 + 7992000*b + 3992000) +
  p^4 * (3000000*b^2 + 5997308*b + 2997737) +
  p^5 * (1149000*b^2 + 2297976*b + 1148973) +
  p^6 * (124000*b^2 + 247952*b + 123973)

theorem runtimeBound_le (p inputLength : ℕ) :
    runtimeBound p inputLength ≤ 9 * inputLength +
      200000 * (p + 1)^6 * (SubexpEnumerationPayload.scalarWidth p + 1)^2 := by
  calc
    runtimeBound p inputLength ≤ runtimeBound p inputLength +
        slack p (SubexpEnumerationPayload.scalarWidth p) := Nat.le_add_right _ _
    _ = _ := by
      simp only [runtimeBound, preparationBound, callbackCost, workspaceWidth,
        linearSize, quadraticSize, candidateSize, slack, SubexpLiftRing.baseWidth,
        SubexpEnumerationPayload.scalarWidth, one_mul]
      ring

theorem program_runs_polynomial (p : ℕ) [Fact p.Prime] (bits : List Bool)
    (regs : Fin 14 → Bool) (hvalue : CounterPrograms.value bits = p) :
    ∃ finalRegs,
      BitProgram.RunsIn program
        (9 * bits.length + 200000 * (p + 1)^6 * (SubexpEnumerationPayload.scalarWidth p + 1)^2)
        ((SubexpQuarticPreparation.inputState regs bits).withPC (some program.entry))
        ((outputState finalRegs p).withPC none) := by
  obtain ⟨finalRegs, n, hn, he⟩ := program_runs p bits regs hvalue
  exact ⟨finalRegs, n, hn.trans (runtimeBound_le p bits.length), he⟩

end SubexponentialSAT.SubexpQuarticProducerBounds

end OAI.Algorithms
