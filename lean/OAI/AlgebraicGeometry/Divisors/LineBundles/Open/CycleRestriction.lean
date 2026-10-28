import OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Cycle Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: restriction of graded finite cycles to an open subscheme

The actual open immersion embeds the generic points without changing
support dimension. Restriction retains exactly the coefficients whose
generic points lie in the open. Extending finite cycles by zero gives a
section of this cycle-level restriction map.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme}

theorem schemeDimensionCycleInclusion_apply (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z x.1 = z x :=
  Finsupp.mapDomain_apply_of_injective (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective z x

theorem schemeDimensionCycleInclusion_of_dimension_ne (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) (x : X)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f ≠ d) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z x = 0 := by
  apply Finsupp.mapDomain_of_notMem_range z x
  rintro ⟨y, hy⟩
  exact hx ((congrArg (fun q => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm q) f)
    hy.symm).trans y.2)

variable [AlgebraicGeometry.IsNoetherian X] (i : X ⟶ Y) [IsOpenImmersion i]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The actual embedding of the dimension-graded generic points. -/
def openDimensionPointEmbedding (d : ℕ) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d ↪ Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d where
  toFun x := ⟨i x.1, (ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i f x.1).trans x.2⟩
  inj' := fun _ _ h => Subtype.ext (i.isOpenEmbedding.injective (congrArg Subtype.val h))

/-- Coefficient restriction along the actual open immersion. -/
def openDimensionCycleRestriction (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :=
  Finsupp.lcomapDomain (openDimensionPointEmbedding i f d) (openDimensionPointEmbedding i f d).injective

/-- Extension of a finite cycle by closing its generic points in the ambient scheme. -/
def openDimensionCycleExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (openDimensionPointEmbedding i f d)

theorem openDimensionCycleRestriction_extension (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :
    openDimensionCycleRestriction i f d (openDimensionCycleExtension i f d z) = z :=
  Finsupp.leftInverse_lcomapDomain_mapDomain (openDimensionPointEmbedding i f d)
    (openDimensionPointEmbedding i f d).injective z

theorem openDimensionCycleRestriction_surjective (d : ℕ) :
    Function.Surjective (openDimensionCycleRestriction i f d) :=
  fun z => ⟨openDimensionCycleExtension i f d z, openDimensionCycleRestriction_extension i f d z⟩

/-- Forgetting the grade recovers restriction of all actual point coefficients. -/
theorem openDimensionCycleRestriction_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (i ≫ f) d (openDimensionCycleRestriction i f d z) =
      Finsupp.comapDomain i (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) i.isOpenEmbedding.injective.injOn := by
  ext x
  by_cases hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) = d
  · let q : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d := ⟨x, hx⟩
    have h := schemeDimensionCycleInclusion_apply (i ≫ f) d (openDimensionCycleRestriction i f d z) q
    have hy := schemeDimensionCycleInclusion_apply f d z (openDimensionPointEmbedding i f d q)
    exact h.trans hy.symm
  · have hi : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i x)) f ≠ d :=
      fun h => hx ((ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i f x).symm.trans h)
    exact (schemeDimensionCycleInclusion_of_dimension_ne (i ≫ f) d _ x hx).trans
      (schemeDimensionCycleInclusion_of_dimension_ne f d z (i x) hi).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction.BundleCycles
