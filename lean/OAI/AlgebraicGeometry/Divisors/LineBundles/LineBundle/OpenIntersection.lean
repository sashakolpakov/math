import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSupportDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IntersectionComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportGenericPoint

/-! # Open Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenIntersection.Cycles

noncomputable section

/-! # LineBundleCycles: genuine graded line-bundle cycle intersection commutes with open Chow restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsOpenImmersion i] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem lineBundleCycleIntersection_open_restriction (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ (i ≫ f) d (Intersection.Cycles.lineBundleCycleIntersection (L.pullback i) (i ≫ f) d
      (Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f (d + 1) z)) =
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection L f d z)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x a =>
    by_cases hx : x.val ∈ Set.range i
    · obtain ⟨y, hy⟩ := hx
      let y' : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) (d + 1) :=
        ⟨y, (ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i f y).symm.trans
          ((congrArg (fun t => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm t) f) hy).trans x.property)⟩
      have he : Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f (d + 1) y' = x := Subtype.ext hy
      rw [← he]
      have hr : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f (d + 1)
          (Finsupp.single (Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f (d + 1) y') a) = Finsupp.single y' a :=
        Finsupp.comapDomain_single _ _ _ _
      rw [hr, Intersection.Cycles.lineBundleCycleIntersection_single, Intersection.Cycles.lineBundleCycleIntersection_single,
        map_smul, map_smul, map_smul, IntersectionComparison.Cycles.lineBundleGradedDivisor_class, IntersectionComparison.Cycles.lineBundleGradedDivisor_class]
      apply congrArg (fun t => a • t)
      have H := OpenSupportDivisor.Cycles.lineBundleDivisorOnSupport_open_class i L f d
        (irreducibleSetEquivPoints.symm (i y)) (Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f (d + 1) y').property
      rw [Open.SupportGenericPoint.BundleCycles.openRestrictedSupport_pointClosure] at H
      exact H
    · have hn : ¬ Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback i (irreducibleSetEquivPoints.symm x.val)) := by
        rw [Open.SupportGenericPoint.BundleCycles.openSupportPullback_nonempty_generic, irreducibleSetEquivPoints.apply_symm_apply]
        exact hx
      have : IsEmpty (Open.SupportRestriction.BundleCycles.openSupportPullback i (irreducibleSetEquivPoints.symm x.val)) := not_nonempty_iff.mp hn
      have hr : x ∉ Set.range (Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f (d + 1)) := by
        rintro ⟨y, hy⟩
        exact hx ⟨y.val, congrArg Subtype.val hy⟩
      have hz : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f (d + 1) (Finsupp.single x a) = 0 :=
        Finsupp.comapDomain_single_of_not_mem_range hr a _
      rw [hz, map_zero, map_zero, Intersection.Cycles.lineBundleCycleIntersection_single, map_smul, map_smul,
        IntersectionComparison.Cycles.lineBundleGradedDivisor_class, OpenSupportDivisor.Cycles.lineBundleDivisorOnSupport_open_empty, smul_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenIntersection.Cycles
