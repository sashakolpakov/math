import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift

/-! # Supported Enlargement -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedEnlargement.Constructions

noncomputable section

/-! Enlarging an actual analytic support preserves the finite cycle and
commutes with its canonical relative class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (U : Opens V.analyticSpace) (S T : Set U) (hST : S ⊆ T) (p : ℕ)

def enlargeSupport (D : SupportedLift.Constructions.Map.SupportedSupport V U S p) : SupportedLift.Constructions.Map.SupportedSupport V U T p := ⟨D.val, D.property.trans hST⟩

def enlargeCycle : SupportedLift.Constructions.Map.SupportedCycle V U S p →ₗ[ℚ] SupportedLift.Constructions.Map.SupportedCycle V U T p :=
  Finsupp.lmapDomain ℚ ℚ (enlargeSupport V U S T hST p)

theorem forget_enlargeCycle (c : SupportedLift.Constructions.Map.SupportedCycle V U S p) :
    SupportedLift.Constructions.Map.forgetCycle V U T p (enlargeCycle V U S T hST p c) = SupportedLift.Constructions.Map.forgetCycle V U S p c := by
  change Finsupp.mapDomain Subtype.val (Finsupp.mapDomain (enlargeSupport V U S T hST p) c) =
    Finsupp.mapDomain Subtype.val c
  exact Finsupp.mapDomain_comp.symm

theorem relativeGenerator_enlarge (D : SupportedLift.Constructions.Map.SupportedSupport V U S p) :
    SupportedLift.Constructions.Map.relativeGenerator V U T p (enlargeSupport V U S T hST p D) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (A := Tᶜ) (B := Sᶜ) (fun _ hx hy => hx (hST hy)) (2 * p) (SupportedLift.Constructions.Map.relativeGenerator V U S p D) :=
  (ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
    (A := Tᶜ) (B := Sᶜ) (fun _ hx hy => hx (hST hy)) (SupportedLift.Constructions.Map.supportComplement_mapsTo V U S p D) (2 * p))
    D.val.rationalSupportedCycleClass).symm

theorem relativeClassMap_enlarge (c : SupportedLift.Constructions.Map.SupportedCycle V U S p) :
    SupportedLift.Constructions.Map.relativeClassMap V U T p (enlargeCycle V U S T hST p c) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (A := Tᶜ) (B := Sᶜ) (fun _ hx hy => hx (hST hy)) (2 * p) (SupportedLift.Constructions.Map.relativeClassMap V U S p c) := by
  suffices h : (SupportedLift.Constructions.Map.relativeClassMap V U T p).comp (enlargeCycle V U S T hST p) =
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (A := Tᶜ) (B := Sᶜ) (fun _ hx hy => hx (hST hy)) (2 * p)).hom.comp
        (SupportedLift.Constructions.Map.relativeClassMap V U S p) from LinearMap.congr_fun h c
  apply Finsupp.lhom_ext
  intro D r
  change SupportedLift.Constructions.Map.relativeClassMap V U T p (enlargeCycle V U S T hST p (Finsupp.single D r)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (A := Tᶜ) (B := Sᶜ) (fun _ hx hy => hx (hST hy)) (2 * p)
      (SupportedLift.Constructions.Map.relativeClassMap V U S p (Finsupp.single D r))
  rw [enlargeCycle, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    SupportedLift.Constructions.Map.relativeClassMap_single, SupportedLift.Constructions.Map.relativeClassMap_single, map_smul, relativeGenerator_enlarge]

theorem restrictCycle_class_enlarge (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (A := Tᶜ) (B := Sᶜ) (fun _ hx hy => hx (hST hy)) (2 * p)
      (SupportedLift.Constructions.Map.relativeClassMap V U S p (SupportedLift.Constructions.restrictCycle V U S p c)) =
    SupportedLift.Constructions.Map.relativeClassMap V U T p (SupportedLift.Constructions.restrictCycle V U T p c) := by
  have he : SupportedLift.Constructions.Map.forgetCycle V U T p (enlargeCycle V U S T hST p (SupportedLift.Constructions.restrictCycle V U S p c)) = c :=
    (forget_enlargeCycle V U S T hST p _).trans (SupportedLift.Constructions.forget_restrictCycle V U S p c hc)
  have h := SupportedLift.Constructions.relativeClassMap_eq_restrict_of_local_coefficients V U T p
    (enlargeCycle V U S T hST p (SupportedLift.Constructions.restrictCycle V U S p c)) c (fun D _ => congrArg (fun e => e D) he)
  exact (relativeClassMap_enlarge V U S T hST p (SupportedLift.Constructions.restrictCycle V U S p c)).symm.trans h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedEnlargement.Constructions
