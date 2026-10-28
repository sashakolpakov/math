import OAI.NumberTheory.PadicHodge.GeometricComparison.BettiFiltration
import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearFiltrationT

/-! # Betti Half Dimension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BettiHalfDimension.BettiHodge

noncomputable section

/-! Complex conjugation exchanges the two actual degree-one Hodge pieces, so the first Hodge step has half the ambient dimension. -/

private theorem map_of_involutive {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₛₗ[starRingEnd ℂ] V) (he : Function.Involutive e)
    (P Q : Submodule ℂ V) (hP : ∀ x ∈ P, e x ∈ Q) (hQ : ∀ x ∈ Q, e x ∈ P) :
    P.map e.toLinearMap = Q := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hP y hy
  · intro hx
    exact ⟨e x, hQ x hx, he x⟩

private theorem finrank_of_involutive {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (e : V ≃ₛₗ[starRingEnd ℂ] V) (he : Function.Involutive e)
    (P Q : Submodule ℂ V) (hP : ∀ x ∈ P, e x ∈ Q) (hQ : ∀ x ∈ Q, e x ∈ P) :
    Module.finrank ℂ Q = Module.finrank ℂ P := by
  have hm := map_of_involutive e he P Q hP hQ
  have hd := SemilinearFiltrationT.SemilinearFiltration.finrank (starRingAut (R := ℂ)) (e.submoduleMap P)
  rw [hm] at hd
  exact hd

theorem degreeOne_isCompl (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    IsCompl (X.pureBettiSubspace 1 0) (X.pureBettiSubspace 0 1) := by
  let i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1 := ⟨(1, 0), rfl⟩
  let j : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1 := ⟨(0, 1), rfl⟩
  have hij : i ≠ j := by decide
  have hall : (Set.univ : Set (Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree 1)) = {i, j} := by
    ext t
    simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
    have ht := t.property
    by_cases h : t.val.1 = 1
    · left
      apply Subtype.ext
      apply Prod.ext <;> dsimp [i] <;> omega
    · right
      apply Subtype.ext
      apply Prod.ext <;> dsimp [j] <;> omega
  exact DirectSum.IsInternal.isCompl (A := Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X 1) hij hall
    (Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration X 1).1

theorem hodgePiece_conjugate_finrank (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ)
    [FiniteDimensional ℂ (X.complexCohomology n)] (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) :
    Module.finrank ℂ (Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i)) = Module.finrank ℂ (Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n i) := by
  let e : X.complexCohomology n ≃ₛₗ[starRingEnd ℂ] X.complexCohomology n :=
    LinearEquiv.ofBijective (Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation X n) (Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_involutive X n).bijective
  apply finrank_of_involutive e (Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_involutive X n)
    (Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n i) (Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i))
  · exact Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_mem_swap X n i
  · intro x hx
    change Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation X n x ∈ Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece X n i
    have h := Analysis.HodgeTheory.Decomposition.Core.Constructions.bettiConjugation_mem_swap X n (Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree i) x hx
    rw [Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree_involutive] at h
    exact h

theorem degreeOne_conjugate_finrank (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [FiniteDimensional ℂ (X.complexCohomology 1)] :
    Module.finrank ℂ (X.pureBettiSubspace 0 1) = Module.finrank ℂ (X.pureBettiSubspace 1 0) := by
  have h := hodgePiece_conjugate_finrank X 1 ⟨(1, 0), rfl⟩
  dsimp only [Analysis.HodgeTheory.Decomposition.Core.Constructions.hodgePiece, Analysis.HodgeTheory.Decomposition.Core.Constructions.swapBidegree] at h
  convert h using 1 <;> rfl

theorem degreeOne_half_dimension (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [FiniteDimensional ℂ (X.complexCohomology 1)] :
    2 * Module.finrank ℂ (X.pureBettiSubspace 1 0) =
      Module.finrank ℂ (X.complexCohomology 1) := by
  have hs := Submodule.finrank_add_eq_of_isCompl (degreeOne_isCompl X)
  change Module.finrank ℂ (X.pureBettiSubspace 1 0) + Module.finrank ℂ (X.pureBettiSubspace 0 1) =
    Module.finrank ℂ (X.complexCohomology 1) at hs
  have hd := degreeOne_conjugate_finrank X
  omega

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BettiHalfDimension.BettiHodge
