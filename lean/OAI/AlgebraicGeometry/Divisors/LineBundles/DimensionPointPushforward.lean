import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GenericDimension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass

/-! # Dimension Point Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionPointPushforward.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual residue-weighted point pushforward preserves every dimension grade -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

def dimensionPointPushforward (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (f ≫ g) d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint g d →₀ ℚ) :=
  (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent g d).comp ((IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f).comp (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f ≫ g) d))

theorem dimensionPointPushforward_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (f ≫ g) d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion g d (dimensionPointPushforward f g d z) =
      IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f ≫ g) d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x a =>
    have hs : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f ≫ g) d (Finsupp.single x a) = Finsupp.single x.val a :=
      Finsupp.mapDomain_single
    change Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion g d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent g d
      (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f ≫ g) d (Finsupp.single x a)))) = _
    rw [hs, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single]
    by_cases hx : f.residueDegree x.val = 0
    · rw [hx, Nat.cast_zero, mul_zero, Finsupp.single_zero, map_zero, map_zero]
    · let y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint g d :=
        ⟨f x.val, (Finite.GenericDimension.BundleCycles.pointClosure_dimension_of_nonzeroResidueDegree f g x.val hx).trans x.property⟩
      rw [Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single g d y]
      exact Finsupp.mapDomain_single

theorem dimensionPointPushforward_comp {Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y]
    (h : Y ⟶ Z) (gZ : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (f ≫ (h ≫ gZ)) d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion gZ d
      (dimensionPointPushforward h gZ d (dimensionPointPushforward f (h ≫ gZ) d z)) =
      IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (f ≫ h) (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f ≫ (h ≫ gZ)) d z) := by
  rw [dimensionPointPushforward_forget, dimensionPointPushforward_forget,
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, LinearMap.comp_apply]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionPointPushforward.BundleCycles
