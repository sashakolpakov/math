import OAI.Analysis.HodgeTheory.Decomposition.Definitions
import OAI.Analysis.HodgeTheory.Decomposition.Constructions

/-! # Hodge Filtration -/

namespace OAI.Analysis.HodgeTheory.Decomposition.HodgeFiltration

noncomputable section

/-! The HodgeDecomposition statement, with its proof supplied by the completed development. -/

/-- HodgeDecomposition: Hodge decomposition, conjugation, and de Rham filtration. -/
theorem hodge_decomposition_and_filtration
    (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    DirectSum.IsInternal (Definitions.hodgePiece X n) ∧
    (∃ c : X.complexCohomology n →ₛₗ[starRingEnd ℂ]
        X.complexCohomology n,
      Function.Involutive c ∧
      (∀ ω : X.componentClosedForms n,
        c (X.closedFormBettiClass n ω) =
          X.closedFormBettiClass n (Definitions.conjugateClosed X n ω)) ∧
      (∀ (i : Definitions.Bidegree n) (x : X.complexCohomology n),
        x ∈ Definitions.hodgePiece X n i ↔
          c x ∈ Definitions.hodgePiece X n (Definitions.swapBidegree i))) ∧
    (∀ p : ℤ,
      Definitions.deRhamFiltrationBetti X n p =
        ⨆ (i : Definitions.Bidegree n) (_ : p ≤ (i.val.1 : ℤ)),
          Definitions.hodgePiece X n i) := by
  exact Constructions.hodge_decomposition_and_filtration X n

end

end OAI.Analysis.HodgeTheory.Decomposition.HodgeFiltration
