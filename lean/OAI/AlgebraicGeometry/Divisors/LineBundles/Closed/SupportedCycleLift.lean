import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.CyclePushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction

/-! # Supported Cycle Lift -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedCycleLift.BundleCycles

noncomputable section

/-!
# LineBundleCycles: transporting a supported finite cycle onto a closed subscheme

The actual closed-immersion point map is injective and preserves support
dimension. If every coefficient lies in its range, coefficient restriction
to the closed subscheme recovers the full original cycle under pushforward.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Z : Scheme} (j : Z ⟶ X) [IsClosedImmersion j] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- Coefficient transport to the closed subscheme, before any Chow quotient. -/
def closedSupportedCycleLift (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d →₀ ℚ) :=
  Finsupp.lcomapDomain (CyclePushforward.BundleCycles.closedDimensionPointMap j f d) (CyclePushforward.BundleCycles.closedDimensionPointMap_injective j f d)

/-- No coefficient is lost when the original cycle is actually supported on the closed subscheme. -/
theorem closedSupportedCycleLift_push (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ)
    (hz : ((Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z).support : Set X) ⊆ Set.range j) :
    CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d (closedSupportedCycleLift j f d z) = z := by
  let e : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d ↪ Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d :=
    ⟨CyclePushforward.BundleCycles.closedDimensionPointMap j f d, CyclePushforward.BundleCycles.closedDimensionPointMap_injective j f d⟩
  have hs : ((z.support : Finset (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d)) : Set (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d)) ⊆
      Set.range e := by
    intro q hq
    have hne : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z q.1 ≠ 0 :=
      fun h => (Finsupp.mem_support_iff.mp hq) ((Open.CycleRestriction.BundleCycles.schemeDimensionCycleInclusion_apply f d z q).symm.trans h)
    obtain ⟨y, hy⟩ := hz (Finsupp.mem_support_iff.mpr hne)
    have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) (j ≫ f) = d :=
      (Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion j f y).symm.trans
        ((congrArg (fun x => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f) hy).trans q.2)
    exact ⟨⟨y, hd⟩, Subtype.ext hy⟩
  exact (Finsupp.embDomain_eq_mapDomain e (Finsupp.comapDomain e z e.injective.injOn)).symm.trans
    (Finsupp.embDomain_comapDomain hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedCycleLift.BundleCycles
