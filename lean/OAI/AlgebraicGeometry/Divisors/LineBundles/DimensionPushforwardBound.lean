import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowNe

/-! # Dimension Pushforward Bound -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionPushforwardBound.BundleCycles

noncomputable section

/-! Actual residue-weighted pushforward vanishes when the images
of all cycle supports have smaller dimension than the cycle grade. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (p : X ⟶ Y) (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem dimensionCycleInclusion_support_dimension
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) d →₀ ℚ) (x : X)
    (hx : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) d z x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (p ≫ f) = d := by
  have hr : x ∈ Set.range (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding (p ≫ f) d) := by
    by_contra hn
    exact hx (Finsupp.mapDomain_of_notMem_range _ _ hn)
  obtain ⟨a, rfl⟩ := hr
  exact a.property

theorem dimensionPointPushforward_zero_of_image_dimension
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) d →₀ ℚ)
    (hz : ∀ x, Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) d z x ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (p x)) f < d) :
    DimensionPointPushforward.BundleCycles.dimensionPointPushforward p f d z = 0 := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective f d
  rw [DimensionPointPushforward.BundleCycles.dimensionPointPushforward_forget, map_zero]
  ext y
  apply Proper.BirationalPrincipalDivisor.BundleCycles.pointPushforward_eq_zero_of_degrees
  intro x hx _
  by_contra hn
  have he := Finite.GenericDimension.BundleCycles.pointClosure_dimension_of_nonzeroResidueDegree p f x hn
  have hd := dimensionCycleInclusion_support_dimension p f d z x hx
  have hl := hz x hx
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionPushforwardBound.BundleCycles
