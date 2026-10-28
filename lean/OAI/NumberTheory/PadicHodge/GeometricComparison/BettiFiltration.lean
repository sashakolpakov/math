import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar
import OAI.Analysis.HodgeTheory.Decomposition.Constructions
import OAI.NumberTheory.PadicHodge.GeometricComparison.DegreeOne

/-! # Betti Filtration -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Identify the degree-one analytic Hodge filtration using the proved HodgeDecomposition decomposition. -/

namespace BettiFiltration.BettiHodge

open OAI.Analysis.HodgeTheory.Decomposition.Constructions

theorem degreeOne_filtration (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℤ) :
    Analysis.HodgeTheory.Decomposition.Core.Constructions.deRhamFiltrationBetti X 1 p =
      if p ≤ 0 then ⊤ else if p = 1 then X.pureBettiSubspace 1 0 else ⊥ := by
  rw [(Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration X 1).2.2 p]
  exact DegreeOne.BettiHodge.degreeOne_hodgeSum X (Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration X 1).1 p

end BettiFiltration.BettiHodge

open OAI.Analysis.HodgeTheory.Decomposition.Constructions

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

theorem Geometry.AbelianH1Model.bettiFiltration_eq_analytic (i : ℤ) :
    A.bettiFiltration j P i = Analysis.HodgeTheory.Decomposition.Core.Constructions.deRhamFiltrationBetti (A.smoothProjectiveFiber j P) 1 i :=
  (BettiFiltration.BettiHodge.degreeOne_filtration (A.smoothProjectiveFiber j P) i).symm

theorem Geometry.AbelianH1Model.bettiHodge_internal :
    DirectSum.IsInternal (Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece (A.smoothProjectiveFiber j P) 1) :=
  (Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration (A.smoothProjectiveFiber j P) 1).1

/-- Conjugation is induced by conjugating actual closed smooth forms. -/
def Geometry.AbelianH1Model.complexBettiConjugation : A.ComplexBetti j →ₛₗ[starRingEnd ℂ] A.ComplexBetti j :=
  Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation (A.smoothProjectiveFiber j P) 1

theorem Geometry.AbelianH1Model.complexBettiConjugation_class
    (ω : (A.smoothProjectiveFiber j P).componentClosedForms 1) :
    A.complexBettiConjugation j P ((A.smoothProjectiveFiber j P).closedFormBettiClass 1 ω) =
      (A.smoothProjectiveFiber j P).closedFormBettiClass 1
        (Analysis.HodgeTheory.Decomposition.Core.Constructions.conjugateClosed (A.smoothProjectiveFiber j P) 1 ω) :=
  Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_class (A.smoothProjectiveFiber j P) 1 ω

theorem Geometry.AbelianH1Model.complexBettiConjugation_involutive :
    Function.Involutive (A.complexBettiConjugation j P) :=
  Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_involutive (A.smoothProjectiveFiber j P) 1

theorem Geometry.AbelianH1Model.complexBettiConjugation_mem_iff (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1) (x : A.ComplexBetti j) :
    x ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece (A.smoothProjectiveFiber j P) 1 i ↔
      A.complexBettiConjugation j P x ∈
        Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece (A.smoothProjectiveFiber j P) 1 (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i) :=
  Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_mem_iff (A.smoothProjectiveFiber j P) 1 i x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
