import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DivisorChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection.Cycles

noncomputable section

section

/-! # LineBundleCycles: actual line-bundle rational-section divisors on arbitrary closed integral supports -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

def lineBundleDivisorOnSupport (W : IrreducibleCloseds X) : X →₀ ℚ :=
  Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) (L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι W)).rationalSectionPointCycle

theorem lineBundleDivisorOnSupport_at_support (W : IrreducibleCloseds X) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :
    lineBundleDivisorOnSupport L W (CycleClass.Geometric.GenericPoint.reducedSupportι W x) =
      (L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι W)).rationalSectionPointCycle x :=
  Finsupp.mapDomain_apply_of_injective (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective _ x

theorem lineBundleDivisorOnSupport_dimension (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (W : IrreducibleCloseds X) (x : X) (hx : lineBundleDivisorOnSupport L W x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f := by
  have hr : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
    by_contra h
    exact hx (Finsupp.mapDomain_of_notMem_range _ _ h)
  obtain ⟨y, rfl⟩ := hr
  rw [lineBundleDivisorOnSupport_at_support] at hx
  have hd := (L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι W)).rationalSectionPointCycle_dimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f) y hx
  exact (congrArg (fun n => n + 1) (Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι W) f y)).trans hd

def lineBundleDivisorOnSupportWithCoefficient (W : IrreducibleCloseds X)
    (a : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionFieldˣ) : X →₀ ℚ :=
  Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) ((L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι W)).rationalSectionPointCycleWithCoefficient a)

theorem lineBundleDivisorOnSupportWithCoefficient_eq (W : IrreducibleCloseds X)
    (a : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionFieldˣ) :
    lineBundleDivisorOnSupportWithCoefficient L W a =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W a.val + lineBundleDivisorOnSupport L W := by
  change Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) _ = _
  rw [LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycleWithCoefficient_eq, Finsupp.mapDomain_add]
  congr 1
  exact (Finsupp.embDomain_eq_mapDomain
    ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩ _).symm

theorem lineBundleDivisorOnSupport_class_independent (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (W : IrreducibleCloseds X) (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (a : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionFieldˣ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (lineBundleDivisorOnSupportWithCoefficient L W a) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (lineBundleDivisorOnSupport L W) := by
  rw [lineBundleDivisorOnSupportWithCoefficient_eq, map_add, Point.CycleChow.BundleCycles.pointCycleToChowQ_principal f d W hW, zero_add]

end

section

/-! # LineBundleCycles: the genuine dimension-graded line-bundle intersection operation on cycles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

def lineBundleGradedDivisor (d : ℕ) (W : IrreducibleCloseds X) : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ :=
  Finsupp.comapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) (lineBundleDivisorOnSupport L W)
    (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective.injOn

theorem lineBundleGradedDivisor_forget [LocallyOfFiniteType f] (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (lineBundleGradedDivisor L f d W) = lineBundleDivisorOnSupport L W := by
  have hs : ((lineBundleDivisorOnSupport L W).support : Set X) ⊆ Set.range (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d) := by
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    have hd := lineBundleDivisorOnSupport_dimension L f W x (Finsupp.mem_support_iff.mp hx)
    omega
  exact Finsupp.mapDomain_comapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d)
    (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective (lineBundleDivisorOnSupport L W) hs

def lineBundleCycleIntersection (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Finsupp.linearCombination ℚ (fun x => lineBundleGradedDivisor L f d (irreducibleSetEquivPoints.symm x.val))

theorem lineBundleCycleIntersection_single (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1)) (a : ℚ) :
    lineBundleCycleIntersection L f d (Finsupp.single x a) =
      a • lineBundleGradedDivisor L f d (irreducibleSetEquivPoints.symm x.val) :=
  Finsupp.linearCombination_single ℚ a x

end

/-! # LineBundleCycles: the actual ungraded line-bundle cycle operation and its complete graded comparison -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

def lineBundlePointIntersection : (X →₀ ℚ) →ₗ[ℚ] (X →₀ ℚ) :=
  Finsupp.linearCombination ℚ (fun x => lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x))

theorem lineBundlePointIntersection_single (x : X) (q : ℚ) :
    lineBundlePointIntersection L (Finsupp.single x q) =
      q • lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x) :=
  Finsupp.linearCombination_single ℚ q x

theorem lineBundlePointIntersection_graded (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    lineBundlePointIntersection L (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f (d + 1) z) =
      Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (lineBundleCycleIntersection L f d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x q =>
    have hi : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f (d + 1) (Finsupp.single x q) = Finsupp.single x.val q :=
      Finsupp.mapDomain_single
    rw [hi, lineBundlePointIntersection_single, lineBundleCycleIntersection_single, map_smul,
      lineBundleGradedDivisor_forget L f d _ x.property]

variable [IsIntegral X]

theorem lineBundlePointIntersection_divisor_sum (g : X.functionField)
    (S : Finset X) (hs : (Ord.BundleCycles.principalDivisor X g).support ⊆ S) :
    lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) =
      ∑ x : S, (X.ord g x : ℚ) • lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x.val) := by
  have hq : (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g).support ⊆ S := by
    intro x hx
    apply hs
    apply Finsupp.mem_support_iff.mpr
    intro hz
    apply Finsupp.mem_support_iff.mp hx
    change (Ord.BundleCycles.principalDivisor X g x : ℚ) = 0
    rw [hz, Int.cast_zero]
  rw [lineBundlePointIntersection, Finsupp.linearCombination_apply]
  exact ((RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g).sum_of_support_subset hq
    (fun x q => q • lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x))
    (fun x _ => zero_smul ℚ (lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x)))).trans
    (Finset.sum_coe_sort S (fun x : X => (X.ord g x : ℚ) •
      lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x))).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection.Cycles
