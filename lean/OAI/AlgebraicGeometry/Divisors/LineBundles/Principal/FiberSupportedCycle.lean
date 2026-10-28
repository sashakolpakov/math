import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberOverCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedSupportedLift

/-! # Fiber Supported Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSupportedCycle.BundleCycles

noncomputable section

/-! The existing principal fiber cycle is fully supported on the inverse image of its parent support, with no loss when lifted into common-support cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (s : Γ(Y.left, ⊤)) (d : ℕ)
  (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom (d + 1))

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem principalFiberOverCycle_supported (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d)
    (hz : FiberOverCycle.BundleCycles.principalFiberOverCycle i s d x z ≠ 0) :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm z.val)) ⊆
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val)) := by
  have hcoeff := (FiberOverCycle.BundleCycles.principalFiberOverCycle_apply i s d x z) ▸ hz
  have hpoint := (Scheme.SupportSection.BundleCycles.schemePrincipalSectionPoint_mem Y (irreducibleSetEquivPoints.symm x.val) s (i.left z.val) hcoeff).1
  have hZ : (irreducibleSetEquivPoints.symm z.val : Set X.left) ⊆
      i.left ⁻¹' (irreducibleSetEquivPoints.symm x.val : Set Y.left) :=
    closure_minimal (Set.singleton_subset_iff.mpr hpoint)
      ((irreducibleSetEquivPoints.symm x.val).isClosed.preimage i.left.continuous)
  intro t ht
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range] at ht
  rw [Set.mem_preimage, CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range]
  exact hZ ht

def principalFiberSupportedCycle :
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle X
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val))) d :=
  Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val))) d
    (FiberOverCycle.BundleCycles.principalFiberOverCycle i s d x)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem principalFiberSupportedCycle_forget :
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget X
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val))) d
      (principalFiberSupportedCycle i s d x) = FiberOverCycle.BundleCycles.principalFiberOverCycle i s d x :=
  Scheme.ClosedSupportedLift.BundleCycles.schemeClosed_forget_restrictCycle X _ d _ (principalFiberOverCycle_supported i s d x)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem principalFiberSupportedCycle_push (hzero : Set.range i.left = (Y.left.basicOpen s : Set Y.left)ᶜ) :
    Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward i d
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget X
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val))) d
        (principalFiberSupportedCycle i s d x)) = CartierFiber.BundleCycles.principalCartierGradedCycle s Y.hom d x := by
  rw [principalFiberSupportedCycle_forget]
  exact FiberOverCycle.BundleCycles.principalFiberOverCycle_push i s d x hzero

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSupportedCycle.BundleCycles
