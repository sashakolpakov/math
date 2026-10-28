import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ComplementEtalePullback

/-! # Residual Neighborhood Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ResidualNeighborhoodEtalePullback.Construction

noncomputable section

/-! Monomial factors and residual-order neighborhoods pull back along the actual comparison map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem boundaryMonomialSheaf_comap {X Y : Scheme} {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (a : β → ℕ) (q : Y ⟶ X) :
    (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a).comap q = Global.MixedBoundary.Construction.boundaryMonomialSheaf (fun l => (D l).comap q) a := by
  rw [Global.MixedBoundary.Construction.boundaryMonomialSheaf, Finite.DisjointCenterSequence.Construction.idealSheaf_comap_finset_prod]
  simp only [IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow, Global.MixedBoundary.Construction.boundaryMonomialSheaf]

theorem exists_residual_order_neighborhood_etale_pullback
    {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth g]
    (J : X.IdealSheafData) (K : Y.IdealSheafData) (m : ℕ)
    (q : Y ⟶ X) [Etale q] (hstructure : q ≫ f = g) (hJ : J.comap q = K) :
    ∃ r : (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g K m).toScheme ⟶ (Global.ResidualNeighborhood.Construction.residualOrderDropOpen f J m).toScheme,
      Etale r ∧ IsPullback r (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g K m).ι (Global.ResidualNeighborhood.Construction.residualOrderDropOpen f J m).ι q := by
  have he : (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1)).comap q = Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (m - 1) := by
    rw [Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale, hJ]
    exact DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr _ _ hstructure _ _
  exact Ideal.ComplementEtalePullback.Construction.exists_ideal_complement_etale_pullback q _ _ he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ResidualNeighborhoodEtalePullback.Construction
