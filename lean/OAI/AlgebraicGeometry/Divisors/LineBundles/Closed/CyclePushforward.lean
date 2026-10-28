import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage

/-! # Cycle Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.CyclePushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: closed-immersion pushforward on dimension-graded cycles

Each generic point maps to its actual image point. Closed immersions
preserve its reduced-support dimension and residue field, so the
pushforward keeps the original rational coefficient.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme} (i : X ⟶ Y) [IsClosedImmersion i]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The actual closed-immersion map on points in one dimension grade. -/
def closedDimensionPointMap (d : ℕ) : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d :=
  fun x => ⟨i x.1, (Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion i f x.1).trans x.2⟩

theorem closedDimensionPointMap_injective (d : ℕ) :
    Function.Injective (closedDimensionPointMap i f d) := by
  intro x y h
  exact Subtype.ext (i.isClosedEmbedding.injective (congrArg Subtype.val h))

/-- Pushforward of finite graded cycles along the actual closed immersion. -/
def closedDimensionCyclePushforward (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (closedDimensionPointMap i f d)

@[simp]
theorem closedDimensionCyclePushforward_single (d : ℕ)
    (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d) (q : ℚ) :
    closedDimensionCyclePushforward i f d (Finsupp.single x q) =
      Finsupp.single (closedDimensionPointMap i f d x) q :=
  Finsupp.mapDomain_single

/-- Forgetting the grading gives the full pushforward on all point coefficients. -/
theorem closedDimensionCyclePushforward_forget (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (closedDimensionCyclePushforward i f d z) =
      Finsupp.mapDomain i (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (i ≫ f) d z) := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ z) = Finsupp.mapDomain _ (Finsupp.mapDomain _ z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.CyclePushforward.BundleCycles
