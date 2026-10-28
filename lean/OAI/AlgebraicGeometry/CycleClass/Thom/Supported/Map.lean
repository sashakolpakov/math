import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Intersection
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.MinimalSupport

/-! # Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map

noncomputable section

/-! Finite cycles contained in a fixed algebraic closed set have an actual
supported class. Forgetting the support gives their original geometric class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AbsoluteProductMaps.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Degree.Constructions.Class

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (F : Closeds V.carrier) (p : ℕ)

abbrev SupportedSupport := {Z : Geometric.DimensionCycles.DimensionCycleSupport V p // (Z.val : Set V.carrier) ⊆ F}
abbrev SupportedCycle := SupportedSupport V F p →₀ ℚ

def forgetCycle : SupportedCycle V F p →ₗ[ℚ] Geometric.DimensionCycles.RationalDimensionCycle V p :=
  Finsupp.lmapDomain ℚ ℚ (fun Z : SupportedSupport V F p => Z.val)

local notation "T" => TopCat.of V.analyticSpace
local notation "O" => (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ

theorem supportComplement_subset (Z : SupportedSupport V F p) :
    O ⊆ (Set.range Z.val.analyticInclusion)ᶜ := by
  intro x hx hz
  rw [Z.val.range_analyticInclusion] at hz
  exact hx (Z.property hz)

def relativeGenerator (Z : SupportedSupport V F p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T O (2 * p) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T)
    (supportComplement_subset V F p Z) (2 * p) Z.val.rationalSupportedCycleClass

def relativeClassMap : SupportedCycle V F p →ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) T O (2 * p) :=
  Finsupp.linearCombination ℚ (relativeGenerator V F p)

def absoluteClassMap : SupportedCycle V F p →ₗ[ℚ] V.rationalCohomology (p + p) :=
  ((eqToHom (congrArg V.rationalCohomology (two_mul p))).hom.comp
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T O (2 * p)).hom).comp
      (relativeClassMap V F p)

theorem relativeGenerator_absolute (Z : SupportedSupport V F p) :
    eqToHom (congrArg V.rationalCohomology (two_mul p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T O (2 * p) (relativeGenerator V F p Z)) =
      Z.val.geometricCycleClass := by
  rw [← GeometricTrace.Constructions.HigherThom.rationalCycleClass_eq_geometric Z.val, Cycle.Degree.Constructions.Class.rationalCycleClass_as_cast Z.val]
  unfold relativeGenerator
  rw [ExteriorCupForget.Constructions.relativeInclusion_pullback, AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, ConcreteCategory.id_apply]
  exact AbsoluteProductMaps.Constructions.absoluteDegreeCast_apply T (two_mul p) _

theorem absoluteClassMap_eq_geometric :
    absoluteClassMap V F p = (V.geometricCycleClassMap p).comp (forgetCycle V F p) := by
  apply Finsupp.lhom_ext
  intro Z r
  change eqToHom (congrArg V.rationalCohomology (two_mul p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T O (2 * p)
        (relativeClassMap V F p (Finsupp.single Z r))) =
    V.geometricCycleClassMap p (forgetCycle V F p (Finsupp.single Z r))
  rw [relativeClassMap, Finsupp.linearCombination_single, map_smul, map_smul,
    relativeGenerator_absolute]
  simp only [forgetCycle, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single]

theorem relativeClassMap_forget (d : SupportedCycle V F p) :
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (two_mul p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T O (2 * p) (relativeClassMap V F p d)) =
      V.geometricCycleClassMap p (forgetCycle V F p d) := by
  have h := LinearMap.congr_fun (absoluteClassMap_eq_geometric V F p) d
  change eqToHom (congrArg V.rationalCohomology (two_mul p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) T O (2 * p) (relativeClassMap V F p d)) = _ at h
  exact (AbsoluteProductMaps.Constructions.absoluteDegreeCast_apply T (two_mul p) _).symm.trans h

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map
