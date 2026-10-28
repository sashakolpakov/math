import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperReciprocity
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueFamily
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection

/-! # Proper Residue Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueChow.Cycles

noncomputable section

/-! # LineBundleCycles: proper reciprocity kills line-bundle intersection with an actual principal divisor on a normal support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a g : X.functionFieldˣ)
    (hproper : Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g.val).support)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)
    (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)

include hX

theorem properLineBundleResidueContribution_chow (x : {x : X // coheight x = 1}) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (ProperResidueContribution.Cycles.properLineBundleResidueContribution L a g hproper hNormal x) =
      (X.ord g.val x : ℚ) • Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x.val)) := by
  let := hNormal x
  have hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x.val) f = d + 1 := by
    have h := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one f x x.property
    omega
  by_cases ha : L.rationalSectionPointDivisorWithCoefficient a x = 0
  · rw [ProperResidueContribution.Cycles.properLineBundleResidueContribution_zero_section L a g hproper hNormal x ha, map_zsmul,
      L.restrictedRationalSectionPointCycle_class a x x.property ha f d hW]
    exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
  · have hg := ProperResidueContribution.Cycles.properSection_function_order_zero L a g hproper x ha
    rw [ProperResidueContribution.Cycles.properLineBundleResidueContribution_nonzero_section L a g hproper hNormal x ha, map_neg, map_zsmul,
      Point.CycleChow.BundleCycles.pointCycleToChowQ_principal f d _ hW, smul_zero, neg_zero, hg, Int.cast_zero, zero_smul]

theorem properLineBundleResidueCycle_chow :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (ProperResidueFamily.Cycles.properLineBundleResidueCycle L a g hproper hNormal) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g.val)) := by
  classical
  rw [ProperResidueFamily.Cycles.properLineBundleResidueCycle_sum, map_sum,
    Intersection.Cycles.lineBundlePointIntersection_divisor_sum L g.val (ProperResidueFamily.Cycles.properLineBundleResidueSupport L a g) Finset.subset_union_right,
    map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_smul]
  exact properLineBundleResidueContribution_chow L a g hproper hNormal f d hX
    ⟨x, ProperResidueFamily.Cycles.properLineBundleResidueSupport_coheight L a g x⟩

include a hproper hNormal in
theorem lineBundlePointIntersection_principal_zero_of_proper :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g.val)) = 0 := by
  rw [← properLineBundleResidueCycle_chow L a g hproper hNormal f d hX,
    ProperReciprocity.Cycles.properLineBundleResidueCycle_zero L a g hproper hNormal f, map_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueChow.Cycles
