import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowOver
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Chow Point Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass.BundleCycles

noncomputable section

/-! # LineBundleCycles: closed and isomorphism Chow pushforwards on actual point-cycle classes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

theorem closedPushforward_dimensionComponent (d : ℕ) (z : X →₀ ℚ) :
    Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d (Finsupp.mapDomain i z) =
      CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (i ≫ f) d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [Finsupp.mapDomain_add, map_add, hz, hw]
  | single x q =>
    by_cases hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) = d
    · let x' : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d := ⟨x, hx⟩
      rw [Finsupp.mapDomain_single, Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single (i ≫ f) d x']
      exact (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single f d (CyclePushforward.BundleCycles.closedDimensionPointMap i f d x') _).trans
        (CyclePushforward.BundleCycles.closedDimensionCyclePushforward_single i f d x' q).symm
    · have hy : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i x)) f ≠ d :=
        fun h => hx ((Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion i f x).symm.trans h)
      rw [Finsupp.mapDomain_single, Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off f d _ _ hy,
        Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single_off (i ≫ f) d _ _ hx, map_zero]

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [LocallyOfFiniteType f]

theorem closedChowPushforward_pointClass (d : ℕ) (z : X →₀ ℚ) :
    ChowPushforward.BundleCycles.closedChowPushforward i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.mapDomain i z) := by
  change DimensionChow.BundleCycles.dimensionCycleToChowQ f d
      (CyclePushforward.BundleCycles.closedDimensionCyclePushforward i f d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent (i ≫ f) d z)) =
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f d (Finsupp.mapDomain i z))
  exact congrArg (DimensionChow.BundleCycles.dimensionCycleToChowQ f d) (closedPushforward_dimensionComponent i f d z).symm

theorem closedChowPushforwardOver_pointClass (g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (h : i ≫ f = g)
    (d : ℕ) (z : X →₀ ℚ) :
    ChowOver.BundleCycles.closedChowPushforwardOver i g f h d (Point.CycleChow.BundleCycles.pointCycleToChowQ g d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.mapDomain i z) := by
  change ChowPushforward.BundleCycles.closedChowPushforward i f d
    (DimensionChow.BundleCycles.dimensionChowTransport h.symm d (Point.CycleChow.BundleCycles.pointCycleToChowQ g d z)) = _
  rw [Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle, closedChowPushforward_pointClass]

theorem schemeIsoChowEquiv_pointClass (e : X ≅ Y) (g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType g] (h : e.hom ≫ f = g) (d : ℕ) (z : X →₀ ℚ) :
    ChowOver.BundleCycles.schemeIsoChowEquiv e g f h d (Point.CycleChow.BundleCycles.pointCycleToChowQ g d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.mapDomain e.hom z) :=
  closedChowPushforwardOver_pointClass e.hom f g h d z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass.BundleCycles
