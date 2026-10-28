import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CodimensionPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenPointChow

/-! # Codimension Set -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CodimensionSet.BundleCycles

noncomputable section

/-! The codimension component of a projective cycle retains exactly
the coefficients whose actual support has that codimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem cyclePointEmbedding_range (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    Set.range (Chow.BundleCycles.cyclePointEmbedding X p) =
      {x | X.supportCodimension (irreducibleSetEquivPoints.symm x) = p} := by
  ext x
  constructor
  · rintro ⟨Z, rfl⟩
    change X.supportCodimension (irreducibleSetEquivPoints.symm (irreducibleSetEquivPoints Z.val)) = p
    rw [irreducibleSetEquivPoints.symm_apply_apply]
    exact Z.property
  · intro hx
    exact ⟨⟨irreducibleSetEquivPoints.symm x, hx⟩, irreducibleSetEquivPoints.apply_symm_apply x⟩

theorem pointCycle_projectiveCodimensionComponent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z : X.carrier →₀ ℚ) :
    Chow.BundleCycles.pointCycle X p (CodimensionPointClass.BundleCycles.projectiveCodimensionComponent X p z) =
      Point.CycleSet.BundleCycles.pointCycleSetPart {x | X.supportCodimension (irreducibleSetEquivPoints.symm x) = p} z := by
  change Finsupp.embDomain (Chow.BundleCycles.cyclePointEmbedding X p)
    (Finsupp.comapDomain (Chow.BundleCycles.cyclePointEmbedding X p) z (Chow.BundleCycles.cyclePointEmbedding X p).injective.injOn) = _
  rw [Finsupp.embDomain_eq_mapDomain, ← ClopenPointChow.BundleCycles.pointCycleSetPart_range, cyclePointEmbedding_range]
  exact (Chow.BundleCycles.cyclePointEmbedding X p).injective

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CodimensionSet.BundleCycles
