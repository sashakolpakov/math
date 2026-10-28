import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass

/-! # Point Class Off Grade -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PointClassOffGrade.BundleCycles

noncomputable section

/-! A cycle in one dimension grade contributes zero in every other grade. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem schemeDimensionComponent_inclusion_off {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (d e : ℕ) (hde : d ≠ e) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f e (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) = 0 := by
  ext x
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) z x.val = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨y, hy⟩
  apply hde
  exact y.property.symm.trans
    ((congrArg (fun t => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm t) f) hy).trans x.property)

theorem pointCycleToChowQ_inclusion_off {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d e : ℕ) (hde : d ≠ e) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f e (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) = 0 := by
  change DimensionChow.BundleCycles.dimensionCycleToChowQ f e (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f e (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z)) = 0
  rw [schemeDimensionComponent_inclusion_off f d e hde, map_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PointClassOffGrade.BundleCycles
