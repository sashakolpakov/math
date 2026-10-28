import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CyclePartition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass

/-! # Cycle Dimension Decomposition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleDimensionDecomposition.BundleCycles

noncomputable section

/-! Every actual finite point cycle is the sum of its finitely many
nonempty dimension components. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def pointCycleDimensionGrades {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (z : X →₀ ℚ) : Finset ℕ := by
  classical
  exact z.support.image (fun x => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f)

theorem pointCycle_dimension_decomposition {X : Scheme.{0}} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (z : X →₀ ℚ) :
    ∑ d : {n // n ∈ pointCycleDimensionGrades f z},
      Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d.val (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d.val z) = z := by
  classical
  apply CyclePartition.BundleCycles.pointCycle_finitePartition_of_support
    (fun d : {n // n ∈ pointCycleDimensionGrades f z} => Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d.val)
    (fun d => Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d.val) (fun d => (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d.val).injective) z
  intro x hx
  let d := Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f
  have hd : d ∈ pointCycleDimensionGrades f z := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  refine ⟨⟨d, hd⟩, ⟨⟨x, rfl⟩, rfl⟩, ?_⟩
  rintro e ⟨u, hu⟩
  apply Subtype.ext
  exact u.property.symm.trans (congrArg (fun x =>
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f) hu)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleDimensionDecomposition.BundleCycles
