import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowInjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowSurjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass

/-! # Chow Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowEquiv.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: genuine Chow homotopy invariance for the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineChowExtension_zeroChowMap (d : ℕ)
    (a : DimensionChow.BundleCycles.DimensionChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)) :
    ChowExtension.BundleCycles.affineLineChowExtension X f d (ZeroChow.BundleCycles.affineLineZeroChowMap X f d a) = a := by
  obtain ⟨b, rfl⟩ := ChowSurjective.BundleCycles.affineLineChowExtension_surjective X f d a
  rw [ChowInjective.BundleCycles.affineLineZeroChowMap_extension]

def affineLineChowEquiv (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) :=
  LinearEquiv.ofBijective (ChowExtension.BundleCycles.affineLineChowExtension X f d)
    ⟨ChowInjective.BundleCycles.affineLineChowExtension_injective X f d, ChowSurjective.BundleCycles.affineLineChowExtension_surjective X f d⟩

theorem affineLineChowEquiv_apply (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    affineLineChowEquiv X f d a = ChowExtension.BundleCycles.affineLineChowExtension X f d a := rfl

theorem affineLineChowEquiv_symm_apply (d : ℕ)
    (a : DimensionChow.BundleCycles.DimensionChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)) :
    (affineLineChowEquiv X f d).symm a = ZeroChow.BundleCycles.affineLineZeroChowMap X f d a := by
  apply ChowInjective.BundleCycles.affineLineChowExtension_injective X f d
  exact ((affineLineChowEquiv X f d).apply_symm_apply a).trans
    (affineLineChowExtension_zeroChowMap X f d a).symm

end

/-! # LineBundleCycles: affine-line Chow homotopy invariance on arbitrary finite point cycles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

omit [AlgebraicGeometry.IsNoetherian X] in
theorem affineLineExtension_dimensionComponent (d : ℕ) (z : X →₀ ℚ) :
    Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z) =
      CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x q =>
    change Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) (Finsupp.single x q)) = _
    rw [Finsupp.mapDomain_single]
    by_cases hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d
    · let x' : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d := ⟨x, hx⟩
      rw [Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single f d x']
      exact (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (CycleGrading.BundleCycles.affineLineDimensionPointMap X f d x') q).trans Finsupp.mapDomain_single.symm
    · have hy : Foundations.Scheme.SupportDimension.supportTranscendenceDimension
          (irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x))
            (Charts.BundleCycles.affineLineProjection X ≫ f) ≠ d + 1 := by
        rw [CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension]
        omega
      rw [Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) _ _ hy,
        Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off f d _ _ hx, map_zero]

theorem affineLineChowEquiv_pointClass (d : ℕ) (z : X →₀ ℚ) :
    affineLineChowEquiv X f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z) := by
  change DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
      (CycleGrading.BundleCycles.affineLineGradedCycleExtension X f d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d z)) =
    DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
      (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z))
  rw [affineLineExtension_dimensionComponent]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowEquiv.BundleCycles
