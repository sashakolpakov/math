import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RegularAmbient
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.NormalRestriction

/-! # Supported Open Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedOpenPullback.BundleCycles

noncomputable section

/-! Canonical supported cycle classes restrict under actual ambient open
immersions, including singular integral supports and codimension zero. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionTarget.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (i : X ⟶ Y) [IsOpenImmersion i.left]
    (B : IrreducibleCloseds Y.left) [Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback i.left B)]

local notation "A" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles.openRestrictedSupport i.left B
local notation "GX" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen X A
local notation "GY" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B
local notation "TX" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
local notation "TY" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
local notation "SX" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X A))ᶜ
local notation "SY" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y B))ᶜ
local notation "JX" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion X A))ᶜ
local notation "JY" => (Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B))ᶜ

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeOpen_support_mapsTo : Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i) SX SY := by
  intro x hx hy
  exact hx ((Set.ext_iff.mp (Open.SupportSquare.BundleCycles.openSupportInclusion_pointRange i B) x).mpr hy)

theorem schemeSupportedCycleClass_openPullback (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (schemeOpen_support_mapsTo i B) (2 * p) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp) =
      SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X A p (Open.SupportOver.BundleCycles.openRestrictedSupportOver_codimension i B p hp) := by
  apply SupportedCycleClass.BundleCycles.schemeSupportedCycleClass_unique X A p (Open.SupportOver.BundleCycles.openRestrictedSupportOver_codimension i B p hp)
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion TX (GX : Set TX)
  let g := Open.RegularAmbient.BundleCycles.openRegularAmbientTopMap i B
  have hj : Set.MapsTo j JX SX :=
    CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo TX SX GX JX (SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq X A)
  have hg : Set.MapsTo g JX JY := Open.RegularAmbient.BundleCycles.openRegularAmbientTopMap_mapsTo i B
  have hy : Set.MapsTo (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion TY (GY : Set TY)) JY SY :=
    CycleClass.Thom.Open.RestrictionTarget.Constructions.openRestrictionMapsTo TY SY GY JY (SupportedCycleClass.BundleCycles.schemeRegularSupportComplement_eq Y B)
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      hj (schemeOpen_support_mapsTo i B) (2 * p)) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp)
  have h₂ := ConcreteCategory.congr_hom
    (CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr
      (Open.RegularAmbient.BundleCycles.openRegularAmbientTopMap_toAmbient i B).symm
      ((schemeOpen_support_mapsTo i B).comp hj) (hy.comp hg) (2 * p))
    (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp)
  have h₃ := SchemeCycle.NormalRestriction.BundleCycles.schemeSupportedCycleClass_regularPairPullback Y B p hp g JX hg
  exact h₁.trans (h₂.trans (h₃.trans (Open.RegularAmbient.BundleCycles.schemeRegularSupportThomClass_openPullback i B p hp)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedOpenPullback.BundleCycles
