import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.GradedOverRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.PreimageSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportGenericPoint

/-! # Closed Cycle Open Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleOpenRestriction.BundleCycles

noncomputable section

/-! The actual open restriction of a finite supported cycle, with the original coefficients at precisely the surviving graded points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsOpenImmersion i.left] (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (d : ℕ)

def schemeClosedCycleOpenRestriction : OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle Y F d →ₗ[ℚ]
    OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d :=
  (Finsupp.lsubtypeDomain {x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d |
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm x.val)) ⊆ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F}).comp
    ((Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction i d).comp (OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget Y F d))

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeClosedCycleOpenRestriction_apply (c : OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle Y F d) :
    schemeClosedCycleOpenRestriction i F d c =
    OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d
      (Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction i d (OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget Y F d c)) := rfl

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [IsOpenImmersion (Over.Hom.left i)] in
theorem schemeClosedRestrictCycle_single (z : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d) (r : ℚ) :
    OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d (Finsupp.single z.val r) = Finsupp.single z r := by
  classical
  ext w
  change Finsupp.single z.val r w.val = Finsupp.single z r w
  simp only [Finsupp.single_apply, Subtype.val_inj]

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeClosedCycleOpenRestriction_single (x : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint Y F d)
    (z : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d)
    (hz : Open.GradedOverRestriction.BundleCycles.openOverDimensionPointEmbedding i d z.val = x.val) (r : ℚ) :
    schemeClosedCycleOpenRestriction i F d (Finsupp.single x r) = Finsupp.single z r := by
  have hf : OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget Y F d (Finsupp.single x r) = Finsupp.single x.val r :=
    Finsupp.mapDomain_single
  rw [schemeClosedCycleOpenRestriction_apply, hf, ← hz, Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction_single,
    schemeClosedRestrictCycle_single]

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeClosedCycleOpenRestriction_single_off (x : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint Y F d)
    (hx : x.val.val ∉ Set.range i.left) (r : ℚ) :
    schemeClosedCycleOpenRestriction i F d (Finsupp.single x r) = 0 := by
  have hf : OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget Y F d (Finsupp.single x r) = Finsupp.single x.val r :=
    Finsupp.mapDomain_single
  rw [schemeClosedCycleOpenRestriction_apply, hf, Open.GradedOverRestriction.BundleCycles.openOverGradedRestriction_single_off i d x.val r hx]
  rfl

omit [AlgebraicGeometry.IsIntegral X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeClosedOpenPoint_support (x : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint Y F d)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) (hz : Open.GradedOverRestriction.BundleCycles.openOverDimensionPointEmbedding i d z = x.val) :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm z.val)) ⊆ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F := by
  have he : i.left z.val = x.val.val := congrArg Subtype.val hz
  have hZ : (irreducibleSetEquivPoints.symm z.val : Set X.left) =
      i.left ⁻¹' (irreducibleSetEquivPoints.symm x.val.val : Set Y.left) := by
    rw [← he, ← Open.SupportRestriction.BundleCycles.openRestrictedSupport_coe i.left, Open.SupportGenericPoint.BundleCycles.openRestrictedSupport_pointClosure]
  have hr := SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_pointRange i (irreducibleSetEquivPoints.symm x.val.val)
    (irreducibleSetEquivPoints.symm z.val) hZ
  intro t ht
  exact x.property ((Set.ext_iff.mp hr t).mp ht)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleOpenRestriction.BundleCycles
