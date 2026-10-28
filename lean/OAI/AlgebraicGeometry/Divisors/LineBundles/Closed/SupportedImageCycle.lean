import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedOverPushforward
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage

/-! # Supported Image Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedImageCycle.BundleCycles

noncomputable section

/-! Actual closed-immersion pushforward of finite supported cycles preserves every coefficient and places each full image support in the same intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (d : ℕ)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem closedSupportedImagePoint_subset (x : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d) :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i (irreducibleSetEquivPoints.symm x.val.val))) ⊆ Set.range v := by
  rw [CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.supportImage_range]
  rintro _ ⟨z, rfl⟩
  exact x.property (Set.mem_range_self z)

def closedSupportedImagePoint (x : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d) :
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d :=
  ⟨Finite.GradedOverPushforward.BundleCycles.finiteOverDimensionPoint i d x.val, by
    rw [Finite.GradedOverPushforward.BundleCycles.finiteOverDimensionPoint_support]
    intro y hy
    refine ⟨?_, closedSupportedImagePoint_subset i v d x hy⟩
    rw [CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.supportImage_range] at hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val.val) z, rfl⟩⟩

def closedSupportedImageCycle : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d →ₗ[ℚ]
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d :=
  Finsupp.lmapDomain ℚ ℚ (closedSupportedImagePoint i v d)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem closedSupportedImageCycle_single
    (x : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d) (r : ℚ) :
    closedSupportedImageCycle i v d (Finsupp.single x r) = Finsupp.single (closedSupportedImagePoint i v d x) r :=
  Finsupp.mapDomain_single

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem closedSupportedImageCycle_forget
    (c : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d) :
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d
      (closedSupportedImageCycle i v d c) =
    Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward i d (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c e hc he => simp only [map_add, hc, he]
  | single x r =>
    have hx : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d
        (Finsupp.single x r) = Finsupp.single x.val r := Finsupp.mapDomain_single
    have hy : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d
        (Finsupp.single (closedSupportedImagePoint i v d x) r) = Finsupp.single (Finite.GradedOverPushforward.BundleCycles.finiteOverDimensionPoint i d x.val) r :=
      Finsupp.mapDomain_single
    rw [closedSupportedImageCycle_single, hx, hy, Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward_single,
      IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle.residueDegree_immersion, Nat.cast_one, mul_one]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedImageCycle.BundleCycles
