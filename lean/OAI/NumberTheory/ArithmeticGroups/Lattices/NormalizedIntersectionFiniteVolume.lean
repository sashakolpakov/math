import OAI.NumberTheory.ArithmeticGroups.Lattices.NormalizedIntersectionSplitFactors
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.FromCompactSplitFactors

/-! # Normalized Intersection Finite Volume -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The normalized translated ambient Siegel intersection has
finite intrinsic right Haar measure. -/

open _root_.ContinuousLinearMap _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem KillingSplit.Construction.KillingSplitWeightData.normalized_intersection_inverseHaar_lt_top
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    [MeasurableSpace (L →L[ℝ] L)ˣ] [BorelSpace (L →L[ℝ] L)ˣ]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement)) (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd)
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (μ : Measure (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) [IsHaarMeasure μ]
    (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L))) (hC : IsCompact C)
    (t : ℝ) (ht : 0 ≤ t) (σ : Equiv.Perm (Fin (Module.finrank ℝ L)))
    (v : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L)) (hv : p.intrinsicProjection v = 1) :
    μ.inv {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | g.val ∈
      OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet d.basis (PermutationMatrixUnits.Construction.permutationMatrixUnit σ * v.val) t C} < ⊤ := by
  obtain ⟨Q, hQ, hfactor⟩ := d.normalized_intersection_compact_split_factors hd p hsep hadj hDadj C hC t ht σ v hv
  obtain ⟨c, _, hambient⟩ := OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet_subset_qr_translate d.basis
    (PermutationMatrixUnits.Construction.permutationMatrixUnit σ * v.val) t C hC
  exact d.inverseHaar_lt_top_of_compact_split_factors hB hK hadj hDadj μ Q hQ
    ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis).symm (PermutationMatrixUnits.Construction.permutationMatrixUnit σ * v.val))
    t c ht _ (fun g hg => hfactor g hg) (fun g hg => hambient g.val hg)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
