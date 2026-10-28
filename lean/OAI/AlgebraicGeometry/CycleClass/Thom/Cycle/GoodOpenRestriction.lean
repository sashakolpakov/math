import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open
import OAI.AlgebraicGeometry.CycleClass.Geometric.Extension

/-! # Good Open Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.GoodOpenRestriction.Constructions

noncomputable section

/-! Actual supported cycle-degree cohomology on an arbitrary analytic neighborhood is unchanged by deleting the omitted boundary of any dense algebraic support open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open.Constructions.Construction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (W : D.scheme.Opens) (hW : genericPoint D.scheme ∈ W) (U : Opens V.analyticSpace)

local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)

theorem supportComplement_subset_goodOpen :
    AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U ⊆
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ := by
  intro x hx h
  apply hx
  rw [D.range_analyticInclusion]
  exact ProperImage.Open.Constructions.Construction.supportOpenBoundary_subset D W h

include hW in
theorem cycleOpen_goodRestriction_isIso :
    IsIso (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U) (2 * p)) := by
  have hc (Z : IrreducibleCloseds V.carrier) (hZ : (Z : Set V.carrier) ⊆ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W) :
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap + (p + 1) ≤
        Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
    have h := ProperImage.Open.Constructions.Construction.supportOpenBoundary_codimension D W hW Z hZ
    have hdim := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V Z
    omega
  exact Scheme.OpenSupportRemoval.Constructions.open_relativeRestriction_isIso V.toOver (ProperImage.Open.Constructions.Construction.supportOpenBoundary D W) (p + 1) hc U
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U)
    (supportComplement_subset_goodOpen D W U) (2 * p) (by omega)

include hW in
theorem cycleOpen_goodRestriction_injective :
    Function.Injective (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val ∈ ProperImage.Open.Constructions.Construction.supportOpenBoundary D W}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U) (2 * p)) := by
  let := cycleOpen_goodRestriction_isIso D W hW U
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.GoodOpenRestriction.Constructions
