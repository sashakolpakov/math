import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion

/-! # Cycle Single Thom -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.CycleSingleThom.Constructions

noncomputable section

/-! The actual class of a single cycle on an open equals its
coefficient times the canonical Thom class, with the given support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions.Bundle OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (U : Opens V.analyticSpace) (S : Set U) (p : ℕ)
  (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (hZ : (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range Z.analyticInclusion ⊆ S)

theorem restrictCycle_single (r : ℚ) :
    SupportedLift.Constructions.restrictCycle V U S p (Finsupp.single Z r) = Finsupp.single ⟨Z, hZ⟩ r := by
  classical
  ext D
  change (Finsupp.single Z r) D.val = (Finsupp.single (⟨Z, hZ⟩ : SupportedLift.Constructions.Map.SupportedSupport V U S p) r) D
  have h : Z = D.val ↔ (⟨Z, hZ⟩ : SupportedLift.Constructions.Map.SupportedSupport V U S p) = D :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp only [Finsupp.single_apply, h]

theorem relativeClassMap_restrict_single (r : ℚ) :
    SupportedLift.Constructions.Map.relativeClassMap V U S p (SupportedLift.Constructions.restrictCycle V U S p (Finsupp.single Z r)) =
      r • SupportedLift.Constructions.Map.relativeGenerator V U S p ⟨Z, hZ⟩ := by
  rw [restrictCycle_single V U S p Z hZ r, SupportedLift.Constructions.Map.relativeClassMap_single]

variable (hU : (U : Set V.analyticSpace) ⊆ Z.regularAmbientOpen)

include hZ in
theorem singleThom_mapsTo : Set.MapsTo (𝟙 (TopCat.of U)) Sᶜ
    (Set.range (Cycle.RegularOpenImmersion.Constructions.Bundle.cycleOpenImmersion Z U hU).regularComplementInclusion)ᶜ := by
  intro u hu hz
  change u ∈ Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion Z U hU) at hz
  rw [Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_range] at hz
  exact hu (hZ hz)

theorem relativeGenerator_eq_Thom :
    SupportedLift.Constructions.Map.relativeGenerator V U S p ⟨Z, hZ⟩ =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (singleThom_mapsTo V U S p Z hZ hU) (2 * p) (Cycle.RegularOpenImmersion.Constructions.Bundle.cycleOpenImmersion Z U hU).regularThomClass := by
  rw [← Cycle.RegularOpenImmersion.Constructions.Bundle.cycleOpenImmersion_Thom Z U hU]
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of U)) (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
    (singleThom_mapsTo V U S p Z hZ hU) (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_mapsTo Z U hU) (2 * p)) Z.rationalSupportedCycleClass
  simp only [ConcreteCategory.comp_apply, Category.id_comp] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.CycleSingleThom.Constructions
