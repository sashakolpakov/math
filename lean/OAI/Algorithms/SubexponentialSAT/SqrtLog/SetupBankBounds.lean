import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupBanks
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupEnvelope
import OAI.Algorithms.SubexponentialSAT.SubexpSetupArithmeticBounds
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseTableCost
import OAI.Algorithms.SubexponentialSAT.SubexpSetupControlBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Banks

open BitProgram StructuredCalls SubexpSetupProgram SubexpSetupStorage

theorem polynomial_envelope (c : Config) : PolynomialEnvelope (command c) := by
  have h1 : PolynomialEnvelope (selectM c) := by
    obtain ⟨C,q,hC,hq,h⟩ := SubexpSetupArithmeticBounds.selectM_polynomial c
    exact ⟨C,q,hC,hq,fun B a t b ha he => by simpa using h B 0 a t b ha he⟩
  have h2 : PolynomialEnvelope (occurrence c) := by
    obtain ⟨C,q,hC,hq,h⟩ := SubexpSetupArithmeticBounds.occurrence_polynomial c
    exact ⟨C,q,hC,hq,fun B a t b ha he => by simpa using h B 0 a t b ha he⟩
  have h3 : PolynomialEnvelope (thresholdTable c) := by
    obtain ⟨C,q,hC,hq,h⟩ := SubexpSetupPhaseTable.thresholdTable_polynomial c
    exact ⟨C,q,hC,hq,fun B a t b ha he => by simpa using h B 0 a t b ha he⟩
  have h4 : PolynomialEnvelope (clearMany (workspacePorts c)) := by
    obtain ⟨C,q,hC,hq,h⟩ := SubexpSetupControlBounds.cleanup_envelope c
    exact ⟨C,q,hC,hq,fun B a t b ha he => by simpa using h B 0 a t b ha he⟩
  exact h1.seq (h2.seq (h3.seq h4))

/-- Uniform polynomial bounds together with the actual new-schedule producer
postcondition. There is no semantic or running-time callback left to supply. -/
theorem bounded_scheduled_eval (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧
      ∀ B n (a : SetupState c), WordBound B a →
        BinaryArithmetic.toNat (a.stacks (persistent c 4)) = Asymptotic.s n →
        ∃ t b, Eval (command c) t a b ∧ t ≤ C*(B+1)^q ∧
          WordBound (C*(B+1)^q) b ∧ Values c (Asymptotic.s n) b ∧
          (∀ i : Fin 32, i ≠ 23 → i ≠ 24 →
            b.stacks (persistent c i) = a.stacks (persistent c i)) := by
  obtain ⟨C,q,hC,hq,h⟩ := polynomial_envelope c
  refine ⟨C,q,hC,hq,?_⟩
  intro B n a ha hs
  obtain ⟨t,b,he,hv,hf⟩ := scheduled_eval c n a hs
  obtain ⟨ht,hb⟩ := h B a t b ha he
  exact ⟨t,b,he,ht,hb,hv,hf⟩

end SubexponentialSAT.SqrtLog.Setup.Banks

end OAI.Algorithms
