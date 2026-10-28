import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.RelationGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowExtension

/-! # Chow Surjective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowSurjective.BundleCycles

noncomputable section

/-! # LineBundleCycles: surjectivity of the actual dimension-graded affine-line Chow pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineChowExtension_single_mem_range (d : ℕ)
    (y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) (Finsupp.single y 1) ∈
      LinearMap.range (ChowExtension.BundleCycles.affineLineChowExtension X f d) := by
  by_cases hy : y.val ∈ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X))
  · obtain ⟨x, hx⟩ := hy
    have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d := by
      have h := CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension X f x
      rw [hx, y.property] at h
      omega
    let x' : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d := ⟨x, hd⟩
    refine ⟨DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finsupp.single x' 1), ?_⟩
    rw [ChowExtension.BundleCycles.affineLineChowExtension_cycle]
    apply congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1))
    change Finsupp.mapDomain (CycleGrading.BundleCycles.affineLineDimensionPointMap X f d) (Finsupp.single x' 1) = _
    rw [Finsupp.mapDomain_single]
    exact congrArg (fun q => Finsupp.single q (1 : ℚ)) (Subtype.ext hx)
  · obtain ⟨W, g, hW, hg, z, hz⟩ := RelationGrading.BundleCycles.affineLineNonextendedPoint_graded_relation X f d y hy
    have h := congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1)) hz
    rw [map_add, ← ChowExtension.BundleCycles.affineLineChowExtension_cycle,
      DimensionChow.BundleCycles.dimensionCycleToChowQ_principal (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) W hW g hg] at h
    refine ⟨-DimensionChow.BundleCycles.dimensionCycleToChowQ f d z, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h).symm

theorem affineLineChowExtension_surjective (d : ℕ) : Function.Surjective (ChowExtension.BundleCycles.affineLineChowExtension X f d) := by
  intro a
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) a
  change DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) (d + 1) z ∈
    LinearMap.range (ChowExtension.BundleCycles.affineLineChowExtension X f d)
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add z w hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  | single y q =>
    have h := Submodule.smul_mem (LinearMap.range (ChowExtension.BundleCycles.affineLineChowExtension X f d)) q
      (affineLineChowExtension_single_mem_range X f d y)
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one] at h
    exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowSurjective.BundleCycles
