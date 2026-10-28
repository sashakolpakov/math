import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PointSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

/-! # Cycle Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.CyclePushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite pushforward with residue degrees in the actual dimension grading
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) [IsFinite i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

def finiteDimensionPointMap (d : ℕ) : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d → Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d :=
  fun x => ⟨i x.1, (PointSupport.BundleCycles.pointClosure_dimension_finite i f x.1).trans x.2⟩

def finiteDimensionCyclePushforward (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Finsupp.linearCombination ℚ (fun x => Finsupp.single (finiteDimensionPointMap i f d x)
    (i.residueDegree x.1 : ℚ))

theorem finiteDimensionCyclePushforward_single (d : ℕ)
    (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d) (q : ℚ) :
    finiteDimensionCyclePushforward i f d (Finsupp.single x q) =
      Finsupp.single (finiteDimensionPointMap i f d x) (q * (i.residueDegree x.1 : ℚ)) := by
  rw [finiteDimensionCyclePushforward, Finsupp.linearCombination_single, Finsupp.smul_single]
  rfl

theorem finiteDimensionCyclePushforward_forget (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (finiteDimensionCyclePushforward i f d z) =
      IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (i ≫ f) d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x q =>
    rw [finiteDimensionCyclePushforward_single]
    change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d)
      (Finsupp.single (finiteDimensionPointMap i f d x) (q * (i.residueDegree x.1 : ℚ))) =
      IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding (i ≫ f) d) (Finsupp.single x q))
    rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single]
    rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.CyclePushforward.BundleCycles
