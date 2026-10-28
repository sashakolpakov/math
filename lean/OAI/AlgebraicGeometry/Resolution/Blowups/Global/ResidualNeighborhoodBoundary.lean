import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionMonomialBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.AffineBoundaryRestriction

/-! # Residual Neighborhood Boundary -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! The lower-residual-order neighborhood retains a nonzero global monomial exceptional factor and its full boundary atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ResidualNeighborhoodBoundary.Construction.idealSheaf_comap_nonempty_open_ne_bot
    {V X : Scheme} [IsIntegral X] [Nonempty V] (j : V ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) : I.comap j ≠ ⊥ := by
  let : IsDominant j := ⟨j.opensRange.isOpen.dense (Set.range_nonempty j)⟩
  let : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  exact GlobalBlowup.Nonzero.Construction.idealSheaf_comap_ne_bot_of_ker_eq_bot j j.ker_eq_bot I hI

theorem CompanionSequence.Construction.SmoothGlobalCompanionSequence.residualNeighborhood_monomial_boundary
    {m b : ℕ} {X : Scheme} [IsIntegral X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) (hmb : m ≤ b) (hMJ : M * J ≠ ⊥)
    (β : Type) [Fintype β] (D : β → X.IdealSheafData) (a : β → ℕ)
    (hD : ∀ l, D l ≠ ⊥) (hM : M = MixedBoundary.Construction.boundaryMonomialSheaf D a)
    (hcenters : T.integralCenters) (hboundary : T.boundaryCompatible β D) :
    ∃ (γ : Type) (inst : Fintype γ), letI := inst
      ∃ (E : γ → T.residualNeighborhood.toScheme.IdealSheafData) (c : γ → ℕ),
        (∀ l, E l ≠ ⊥) ∧ T.exceptionalIdeal.comap T.residualNeighborhood.ι = MixedBoundary.Construction.boundaryMonomialSheaf E c ∧
        Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (T.residualNeighborhood.ι ≫ (T.toBase ≫ f)) E [Finset.univ]) := by
  let : IsIntegral T.endpoint := T.endpoint_integral
  let : IsIntegral T.residualNeighborhood := T.residualNeighborhood_integral hmb hMJ
  obtain ⟨γ, inst, E, c, hE, he, ⟨A⟩⟩ := T.terminal_monomial_boundary β D a hD hM hcenters hboundary
  let : Fintype γ := inst
  refine ⟨γ, inst, (fun l => (E l).comap T.residualNeighborhood.ι), c, ?_, ?_, ?_⟩
  · intro l
    exact ResidualNeighborhoodBoundary.Construction.idealSheaf_comap_nonempty_open_ne_bot T.residualNeighborhood.ι (E l) (hE l)
  · rw [he, MixedBoundary.Construction.boundaryMonomialSheaf_comap_open]
  · exact ⟨A.comapOpen (T.toBase ≫ f) T.residualNeighborhood.ι⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
