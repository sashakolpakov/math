import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionPointPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.SupportDimensionDrop
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.FiberPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Chow Ne -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowNe.BundleCycles

noncomputable section

section

/-! Proper pushforward on the genuine dimension-graded rational Chow
quotients, proved from the norm and dimension-drop formulas. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y) [IsProper f]
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]

omit [AlgebraicGeometry.IsNoetherian Y] [X.IsSeparated] [Y.IsSeparated] in
theorem properPointSupportNorm_ne_zero (x : X)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY))
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField) (hg : g ≠ 0) :
    PointSupport.BundleCycles.properPointSupportNorm f x g ≠ 0 := by
  let := (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap f x).hom.toAlgebra
  let := PointSupport.BundleCycles.properPointSupport_functionField_finite f gY x hd
  exact Algebra.norm_ne_zero_iff.mpr hg

omit [X.IsSeparated] [Y.IsSeparated] in
theorem dimensionPointPushforward_principal_dimension_eq (d : ℕ) (x : X)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY) = d + 1)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY))
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField) (hg : g ≠ 0) :
    DimensionPointPushforward.BundleCycles.dimensionPointPushforward f gY d
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (f ≫ gY) d (irreducibleSetEquivPoints.symm x) g) =
        Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor gY d (irreducibleSetEquivPoints.symm (f x))
          (PointSupport.BundleCycles.properPointSupportNorm f x g) := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective gY d
  rw [DimensionPointPushforward.BundleCycles.dimensionPointPushforward_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (f ≫ gY) d _ hx,
    PointSupport.BundleCycles.properPushforward_principalPointSupport_of_dimension_eq f gY x hd g hg,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push gY d _ (hd.trans hx)]

omit [AlgebraicGeometry.IsNoetherian Y] in
theorem dimensionPointPushforward_principal_dimension_drop (d : ℕ) (x : X)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY) = d + 1)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) gY <
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY))
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField) (hg : g ≠ 0) :
    DimensionPointPushforward.BundleCycles.dimensionPointPushforward f gY d
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor (f ≫ gY) d (irreducibleSetEquivPoints.symm x) g) = 0 := by
  apply Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion_injective gY d
  rw [DimensionPointPushforward.BundleCycles.dimensionPointPushforward_forget, Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push (f ≫ gY) d _ hx,
    SupportDimensionDrop.BundleCycles.properPushforward_principalPointSupport_of_dimension_drop f gY x hd g hg, map_zero]

theorem dimensionPointPushforward_principal_mem (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (f ≫ gY) d →₀ ℚ)
    (hz : DimensionChow.BundleCycles.IsDimensionPrincipalDivisorQ (f ≫ gY) d z) :
    DimensionPointPushforward.BundleCycles.dimensionPointPushforward f gY d z ∈ DimensionChow.BundleCycles.dimensionRationalEquivalenceQ gY d := by
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  obtain ⟨x, rfl⟩ := irreducibleSetEquivPoints.symm.surjective W
  have hle := SupportDimensionDrop.BundleCycles.properPointSupport_dimension_le f gY x
  rcases hle.eq_or_lt with hd | hd
  · rw [dimensionPointPushforward_principal_dimension_eq f gY d x hW hd g hg]
    exact Submodule.subset_span ⟨irreducibleSetEquivPoints.symm (f x), hd.trans hW,
      PointSupport.BundleCycles.properPointSupportNorm f x g, properPointSupportNorm_ne_zero f gY x hd g hg, rfl⟩
  · rw [dimensionPointPushforward_principal_dimension_drop f gY d x hW hd g hg]
    exact Submodule.zero_mem _

theorem dimensionPointPushforward_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (f ≫ gY) d ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ gY d).comap (DimensionPointPushforward.BundleCycles.dimensionPointPushforward f gY d) := by
  apply Submodule.span_le.mpr
  intro z hz
  exact dimensionPointPushforward_principal_mem f gY d z hz

def properChowPushforward (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ (f ≫ gY) d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ gY d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ (f ≫ gY) d).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ gY d)
    (DimensionPointPushforward.BundleCycles.dimensionPointPushforward f gY d) (dimensionPointPushforward_relations f gY d)

@[simp]
theorem properChowPushforward_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (f ≫ gY) d →₀ ℚ) :
    properChowPushforward f gY d (DimensionChow.BundleCycles.dimensionCycleToChowQ (f ≫ gY) d z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ gY d (DimensionPointPushforward.BundleCycles.dimensionPointPushforward f gY d z) := rfl

end

section

/-! Proper Chow pushforward agrees with actual point pushforward in every dimension component. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

theorem pointPushforward_dimensionComponent (d : ℕ) (z : X →₀ ℚ) :
    Finite.ChowPointClass.BundleCycles.schemeDimensionComponent gY d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f z) =
      DimensionPointPushforward.BundleCycles.dimensionPointPushforward f gY d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (f ≫ gY) d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x q =>
    by_cases hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY) = d
    · let x' : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (f ≫ gY) d := ⟨x, hx⟩
      rw [Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single (f ≫ gY) d x']
      change Finite.ChowPointClass.BundleCycles.schemeDimensionComponent gY d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (Finsupp.single x q)) =
        Finite.ChowPointClass.BundleCycles.schemeDimensionComponent gY d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f
          (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f ≫ gY) d (Finsupp.single x' q)))
      rw [show Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f ≫ gY) d (Finsupp.single x' q) =
        Finsupp.single x q from Finsupp.mapDomain_single]
    · rw [Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off (f ≫ gY) d x q hx, map_zero, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single]
      by_cases hd : f.residueDegree x = 0
      · rw [hd, Nat.cast_zero, mul_zero, Finsupp.single_zero, map_zero]
      · exact Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off gY d (f x) _
          (fun h => hx ((Finite.GenericDimension.BundleCycles.pointClosure_dimension_of_nonzeroResidueDegree f gY x hd).symm.trans h))

theorem properChowPushforward_pointClass [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated] [IsProper f] [LocallyOfFiniteType gY]
    (d : ℕ) (z : X →₀ ℚ) :
    properChowPushforward f gY d (Point.CycleChow.BundleCycles.pointCycleToChowQ (f ≫ gY) d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ gY d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f z) := by
  change DimensionChow.BundleCycles.dimensionCycleToChowQ gY d
      (DimensionPointPushforward.BundleCycles.dimensionPointPushforward f gY d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (f ≫ gY) d z)) =
    DimensionChow.BundleCycles.dimensionCycleToChowQ gY d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent gY d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f z))
  exact congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ gY d) (pointPushforward_dimensionComponent f gY d z).symm

end

/-! Proper Chow pushforward commutes with an actual open base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U] [E.IsSeparated] [X.IsSeparated]
    [E'.IsSeparated] [U.IsSeparated]
    (p : E ⟶ X) (q : E' ⟶ U) [IsProper p] [IsProper q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (hs : q ≫ i = j ≫ p) (hc : Set.range j = p ⁻¹' Set.range i)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include hc in
theorem properChowPushforward_openSquare (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) :
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d (properChowPushforward p f d α) =
      properChowPushforward q (i ≫ f) d
        (DimensionChow.BundleCycles.dimensionChowTransport (show j ≫ (p ≫ f) = q ≫ (i ≫ f) by
          rw [← Category.assoc, ← hs, Category.assoc]) d
          (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) d α)) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (p ≫ f) d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion (p ≫ f) d z, properChowPushforward_pointClass,
    Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass,
    Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle, properChowPushforward_pointClass,
    Open.FiberPushforward.BundleCycles.openSquare_pointPushforward p i j q hs.symm hc]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowNe.BundleCycles
