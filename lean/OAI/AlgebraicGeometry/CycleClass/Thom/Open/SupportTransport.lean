import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift

/-! # Support Transport -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport.Constructions

noncomputable section

/-! Changing the displayed analytic support along an actual equality
preserves the canonical class of the same finite cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (U : Opens V.analyticSpace) (S T : Set U) (h : S = T) (p : ℕ)

 theorem relativeClassMap_restrict_support_congr (c : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (A := Tᶜ) (B := Sᶜ) (fun _ hx hy => hx (h ▸ hy)) (2 * p)
      (SupportedLift.Constructions.Map.relativeClassMap V U S p (SupportedLift.Constructions.restrictCycle V U S p c)) =
    SupportedLift.Constructions.Map.relativeClassMap V U T p (SupportedLift.Constructions.restrictCycle V U T p c) := by
  subst T
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id, ConcreteCategory.id_apply]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport.Constructions
