import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.CyclePushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction

/-! # Cycle Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.CycleLocalization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: exact localization of dimension-graded finite cycles

For an actual closed immersion whose range is the complement of an open
immersion, precisely the cycles restricting to zero are pushed from the
closed part. The proof uses all coefficients and the actual point maps.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {U X Z : Scheme} [AlgebraicGeometry.IsNoetherian U]
    (i : U ⟶ X) [IsOpenImmersion i] (j : Z ⟶ X) [IsClosedImmersion j]
    (hcomp : Set.range j = (Set.range i)ᶜ) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

include hcomp

/-- A cycle pushed from the closed complement restricts to zero on the open. -/
theorem openDimensionCycleRestriction_closed (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d →₀ ℚ) :
    Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d (Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d z) = 0 := by
  ext x
  change Finsupp.mapDomain (Closed.CyclePushforward.BundleCycles.closedDimensionPointMap j f d) z (Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f d x) = 0
  apply Finsupp.mapDomain_of_notMem_range z _
  rintro ⟨y, hy⟩
  have hp : j y.1 = i x.1 := congrArg Subtype.val hy
  have hn : j y.1 ∉ Set.range i :=
    (congrArg (fun s : Set X => j y.1 ∈ s) hcomp).mp ⟨y.1, rfl⟩
  exact hn ⟨x.1, hp.symm⟩

/-- All coefficients of a cycle vanishing on the open lift to the actual closed complement. -/
theorem exists_closedDimensionCycle_of_zero_restriction (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) (hz : Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction i f d z = 0) :
    ∃ w : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d →₀ ℚ, Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d w = z := by
  let e : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d ↪ Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d :=
    ⟨Closed.CyclePushforward.BundleCycles.closedDimensionPointMap j f d, Closed.CyclePushforward.BundleCycles.closedDimensionPointMap_injective j f d⟩
  have hs : ((z.support : Finset (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d)) : Set (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d)) ⊆
      Set.range e := by
    intro q hq
    have hqz : z q ≠ 0 := Finsupp.mem_support_iff.mp hq
    have hnot : q.1 ∉ Set.range i := by
      rintro ⟨x, hx⟩
      have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) = d :=
        (ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i f x).symm.trans
          ((congrArg (fun y => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) f) hx).trans q.2)
      let p : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d := ⟨x, hd⟩
      have he : Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f d p = q := Subtype.ext hx
      have hzero := congrArg (fun a => a p) hz
      change z (Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding i f d p) = 0 at hzero
      exact hqz ((congrArg z he.symm).trans hzero)
    have hr : q.1 ∈ Set.range j :=
      (congrArg (fun s : Set X => q.1 ∈ s) hcomp).mpr hnot
    obtain ⟨y, hy⟩ := hr
    have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) (j ≫ f) = d :=
      (Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion j f y).symm.trans
        ((congrArg (fun x => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f) hy).trans q.2)
    exact ⟨⟨y, hd⟩, Subtype.ext hy⟩
  refine ⟨Finsupp.comapDomain e z e.injective.injOn, ?_⟩
  exact (Finsupp.embDomain_eq_mapDomain e (Finsupp.comapDomain e z e.injective.injOn)).symm.trans
    (Finsupp.embDomain_comapDomain hs)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.CycleLocalization.BundleCycles
