import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic
import Mathlib.Topology.Clopen

/-! # Qadic Completion Integers -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicCompletionIntegers.CM

noncomputable section

/-! The completion equivalence attached to a q-adic field embedding
preserves the actual valuation rings. -/

open scoped Classical
open _root_.NumberField IsDedekindDomain

theorem closed_iff {X : Type*} [TopologicalSpace X] (S T : Set X)
    (hS : IsClopen S) (hT : IsClopen T) : IsClosed {x | x ∈ S ↔ x ∈ T} := by
  have he : {x | x ∈ S ↔ x ∈ T} = (S ∩ T) ∪ (Sᶜ ∩ Tᶜ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  rw [he]
  exact (hS.isClosed.inter hT.isClosed).union (hS.compl.isClosed.inter hT.compl.isClosed)

variable {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]

theorem integral_iff (f : K →+* ℚ_[q]) (x : (PELModuli.CMPoints.LocalPadic.embeddingPlace f).adicCompletion K) :
    x ∈ (PELModuli.CMPoints.LocalPadic.embeddingPlace f).adicCompletionIntegers K ↔
      ‖PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv f x‖ ≤ 1 := by
  let v := PELModuli.CMPoints.LocalPadic.embeddingPlace f
  have hclosed : IsClosed {x : v.adicCompletion K |
      x ∈ v.adicCompletionIntegers K ↔ ‖PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv f x‖ ≤ 1} := by
    apply closed_iff
    · exact Valued.isClopen_valuationSubring _
    · have h : IsClopen {y : ℚ_[q] | ‖y‖ ≤ 1} := by
        simpa only [Metric.closedBall, dist_zero_right] using
          (IsUltrametricDist.isClopen_closedBall (0 : ℚ_[q]) (one_ne_zero : (1 : ℝ) ≠ 0))
      exact h.preimage (PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_continuous f)
  refine (v.denseRange_algebraMap K).induction_on x hclosed ?_
  intro a
  change Valued.v (a : v.adicCompletion K) ≤ 1 ↔
    ‖PELModuli.CMPoints.LocalPadic.embeddingCompletionHom f
      (FinitePlace.embedding (PELModuli.CMPoints.LocalPadic.embeddingPlace f) a)‖ ≤ 1
  rw [PELModuli.CMPoints.LocalPadic.embeddingCompletionHom_coe]
  rw [HeightOneSpectrum.adicCompletion.valued_coe]
  exact (PELModuli.CMPoints.LocalPadic.embedding_valuation_equiv f).le_one_iff_le_one

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicCompletionIntegers.CM
