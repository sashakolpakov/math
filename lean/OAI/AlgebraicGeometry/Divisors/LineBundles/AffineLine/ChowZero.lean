import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowEquiv

/-! # Chow Zero -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowZero.BundleCycles

noncomputable section

/-! # LineBundleCycles: zero-dimensional Chow classes on the relative affine line vanish -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineLineZeroDimension_point_class (y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (Charts.BundleCycles.affineLineProjection X ≫ f) 0) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) 0 (Finsupp.single y 1) = 0 := by
  have hy : y.val ∉ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) := by
    rintro ⟨x, hx⟩
    have h := CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension X f x
    rw [hx, y.property] at h
    omega
  obtain ⟨W, g, hg, w, hrel⟩ := PointRelation.BundleCycles.affineLineNonextendedPoint_cycle_relation X y.val hy
  have hcoeff : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g y.val = 1 := by
    have h := congrArg (fun z : Charts.BundleCycles.affineLine X →₀ ℚ => z y.val) hrel
    change Finsupp.single y.val (1 : ℚ) y.val +
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) w y.val = _ at h
    rw [Finsupp.single_eq_same, Finsupp.mapDomain_of_notMem_range _ _ hy, add_zero] at h
    exact h.symm
  have hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (Charts.BundleCycles.affineLineProjection X ≫ f) = 1 := by
    have h := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension (Charts.BundleCycles.affineLineProjection X ≫ f) W g y.val (hcoeff ▸ one_ne_zero)
    exact h.symm.trans (congrArg (fun n => n + 1) y.property)
  have hw : w = 0 := by
    ext x
    by_contra hx
    have hneq : Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x ≠ y.val := fun h => hy ⟨x, h⟩
    have h := congrArg (fun z : Charts.BundleCycles.affineLine X →₀ ℚ => z (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x)) hrel
    change Finsupp.single y.val (1 : ℚ) (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) +
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) w
        (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) = _ at h
    rw [Finsupp.single_eq_of_ne hneq, Finsupp.mapDomain_apply_of_injective (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_injective (Charts.BundleCycles.affineLineProjection X)), zero_add] at h
    have hn : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) x) ≠ 0 :=
      fun hz => hx (h.trans hz)
    have hd := Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_dimension (Charts.BundleCycles.affineLineProjection X ≫ f) W g _ hn
    rw [CycleGrading.BundleCycles.affineLineFiberGenericPoint_dimension, hW] at hd
    omega
  rw [hw, map_zero, add_zero] at hrel
  have hgrade : Finsupp.single y 1 = Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (Charts.BundleCycles.affineLineProjection X ≫ f) 0 W g := by
    apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective (Charts.BundleCycles.affineLineProjection X ≫ f) 0
    rw [Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (Charts.BundleCycles.affineLineProjection X ≫ f) 0 W hW]
    exact (show Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (Charts.BundleCycles.affineLineProjection X ≫ f) 0 (Finsupp.single y 1) =
      Finsupp.single y.val 1 from Finsupp.mapDomain_single).trans hrel
  rw [hgrade, DimensionChow.BundleCycles.dimensionCycleToChowQ_principal (Charts.BundleCycles.affineLineProjection X ≫ f) 0 W hW g hg]

theorem affineLineZeroDimension_chow_eq_zero (a : DimensionChow.BundleCycles.DimensionChowQ (Charts.BundleCycles.affineLineProjection X ≫ f) 0) : a = 0 := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (Charts.BundleCycles.affineLineProjection X ≫ f) 0 a
  induction z using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add z w hz hw => rw [map_add, hz, hw, add_zero]
  | single y q =>
    have h := congrArg (fun a => q • a) (affineLineZeroDimension_point_class X f y)
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one, smul_zero] at h
    exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowZero.BundleCycles
