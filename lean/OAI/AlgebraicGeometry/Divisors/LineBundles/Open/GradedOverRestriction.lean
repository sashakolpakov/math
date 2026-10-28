import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportOver

/-! # Graded Over Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.GradedOverRestriction.BundleCycles

noncomputable section

/-! Actual open restriction on finite cycles in the literal source
and target dimension gradings. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [AlgebraicGeometry.IsNoetherian X.left] (i : X ⟶ Y) [IsOpenImmersion i.left]

def openOverDimensionPointEmbedding (d : ℕ) : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d ↪ Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d where
  toFun x := ⟨i.left x.val, by
    have h := ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i.left Y.hom x.val
    rw [i.w] at h
    exact h.trans x.property⟩
  inj' := fun _ _ h => Subtype.ext (i.left.isOpenEmbedding.injective (congrArg Subtype.val h))

def openOverGradedRestriction (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :=
  Finsupp.lcomapDomain (openOverDimensionPointEmbedding i d) (openOverDimensionPointEmbedding i d).injective

theorem openOverGradedRestriction_single (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) (a : ℚ) :
    openOverGradedRestriction i d (Finsupp.single (openOverDimensionPointEmbedding i d x) a) = Finsupp.single x a :=
  Finsupp.comapDomain_single (openOverDimensionPointEmbedding i d) x a
    (openOverDimensionPointEmbedding i d).injective.injOn

theorem openOverGradedRestriction_single_off (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d) (a : ℚ)
    (hx : x.val ∉ Set.range i.left) : openOverGradedRestriction i d (Finsupp.single x a) = 0 := by
  apply Finsupp.comapDomain_single_of_not_mem_range
  rintro ⟨y, hy⟩
  exact hx ⟨y.val, congrArg Subtype.val hy⟩

theorem openOverGradedRestriction_forget (d : ℕ) (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.hom d (openOverGradedRestriction i d a) =
      Finsupp.comapDomain i.left (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion Y.hom d a) i.left.isOpenEmbedding.injective.injOn := by
  ext x
  by_cases hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) X.hom = d
  · let q : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d := ⟨x, hx⟩
    have h := CycleRestriction.BundleCycles.schemeDimensionCycleInclusion_apply X.hom d (openOverGradedRestriction i d a) q
    have hy := CycleRestriction.BundleCycles.schemeDimensionCycleInclusion_apply Y.hom d a (openOverDimensionPointEmbedding i d q)
    exact h.trans hy.symm
  · have hi : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i.left x)) Y.hom ≠ d := by
      intro h
      have he := ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i.left Y.hom x
      rw [i.w] at he
      exact hx (he.symm.trans h)
    exact (CycleRestriction.BundleCycles.schemeDimensionCycleInclusion_of_dimension_ne X.hom d _ x hx).trans
      (CycleRestriction.BundleCycles.schemeDimensionCycleInclusion_of_dimension_ne Y.hom d a (i.left x) hi).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.GradedOverRestriction.BundleCycles
