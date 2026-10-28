import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift

/-! # Cycle Lift -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Supported.CycleLift.Constructions.OpenMap

/-! The canonical supported class of a genuine algebraically supported
cycle restricts to its canonical finite-cycle class on every analytic
open. All maps retain the original cycle coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (F : Closeds V.carrier) (p : ℕ)

local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions.SupportedCycle V F p
local notation "GS" => OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions.SupportedSupport V F p
local notation "T" => TopCat.of V.analyticSpace
local notation "O" => (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ

variable (U : Opens V.analyticSpace)

local notation "S" => Subtype (fun x : U => V.analyticUnderlying (Subtype.val x) ∈ F)

def openSupport (D : GS) : Open.SupportedLift.Constructions.Map.SupportedSupport V U
    {x : U | V.analyticUnderlying x.val ∈ F} p :=
  ⟨D.val, by
    intro x hx
    rw [D.val.range_analyticInclusion] at hx
    exact D.property hx⟩

def openCycle : G →ₗ[ℚ] Open.SupportedLift.Constructions.Map.SupportedCycle V U
    {x : U | V.analyticUnderlying x.val ∈ F} p :=
  Finsupp.lmapDomain ℚ ℚ (openSupport V F p U)

 theorem forget_openCycle (c : G) :
    Open.SupportedLift.Constructions.Map.forgetCycle V U {x : U | V.analyticUnderlying x.val ∈ F} p
      (openCycle V F p U c) = Map.Constructions.forgetCycle V F p c := by
  change Finsupp.mapDomain Subtype.val (Finsupp.mapDomain (openSupport V F p U) c) =
    Finsupp.mapDomain Subtype.val c
  exact Finsupp.mapDomain_comp.symm

 theorem relativeGenerator_open (D : GS) :
    Open.SupportedLift.Constructions.Map.relativeGenerator V U {x : U | V.analyticUnderlying x.val ∈ F} p
      (openSupport V F p U D) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O U (2 * p)
      (Map.Constructions.relativeGenerator V F p D) := by
  exact (ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion T (U : Set V.analyticSpace)) (𝟙 T)
    (A := {x : U | V.analyticUnderlying x.val ∈ F}ᶜ) (B := O)
    (fun _ hx => hx) (Map.Constructions.supportComplement_subset V F p D) (2 * p))
    D.val.rationalSupportedCycleClass).symm

 theorem relativeClassMap_open (c : G) :
    Open.SupportedLift.Constructions.Map.relativeClassMap V U {x : U | V.analyticUnderlying x.val ∈ F} p
      (openCycle V F p U c) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O U (2 * p)
      (Map.Constructions.relativeClassMap V F p c) := by
  suffices h : (Open.SupportedLift.Constructions.Map.relativeClassMap V U {x : U | V.analyticUnderlying x.val ∈ F} p).comp
      (openCycle V F p U) =
    (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O U (2 * p)).hom.comp
      (Map.Constructions.relativeClassMap V F p) from LinearMap.congr_fun h c
  apply Finsupp.lhom_ext
  intro D r
  change Open.SupportedLift.Constructions.Map.relativeClassMap V U {x : U | V.analyticUnderlying x.val ∈ F} p
      (openCycle V F p U (Finsupp.single D r)) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O U (2 * p)
      (Map.Constructions.relativeClassMap V F p (Finsupp.single D r))
  rw [openCycle, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Open.SupportedLift.Constructions.Map.relativeClassMap_single, Map.Constructions.relativeClassMap,
    Finsupp.linearCombination_single, map_smul, relativeGenerator_open]

 theorem restrictCycle_class_of_global (c : G) :
    Open.SupportedLift.Constructions.Map.relativeClassMap V U {x : U | V.analyticUnderlying x.val ∈ F} p
      (Open.SupportedLift.Constructions.restrictCycle V U {x : U | V.analyticUnderlying x.val ∈ F} p
        (Map.Constructions.forgetCycle V F p c)) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O U (2 * p)
      (Map.Constructions.relativeClassMap V F p c) := by
  have h := Open.SupportedLift.Constructions.relativeClassMap_eq_restrict_of_local_coefficients
    V U {x : U | V.analyticUnderlying x.val ∈ F} p (openCycle V F p U c)
    (Map.Constructions.forgetCycle V F p c) (fun C _ => congrArg (fun z => z C) (forget_openCycle V F p U c))
  exact h.symm.trans (relativeClassMap_open V F p U c)

end AlgebraicGeometry.CycleClass.Thom.Supported.CycleLift.Constructions.OpenMap

namespace AlgebraicGeometry.CycleClass.Thom.Supported.CycleLift.Constructions

/-! The actual cycle coefficients provide a canonical lift to an
algebraic closed support; its relative class restricts to the canonical
class on every analytic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CycleLift.Constructions.OpenMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (F : Closeds V.carrier) (p : ℕ)

def liftCycle (c : Geometric.DimensionCycles.RationalDimensionCycle V p) : Map.Constructions.SupportedCycle V F p :=
  Finsupp.subtypeDomain (fun D : Geometric.DimensionCycles.DimensionCycleSupport V p => (D.val : Set V.carrier) ⊆ F) c

 theorem forget_liftCycle (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → (D.val : Set V.carrier) ⊆ F) :
    Map.Constructions.forgetCycle V F p (liftCycle V F p c) = c := by
  classical
  ext D
  by_cases hD : (D.val : Set V.carrier) ⊆ F
  · exact (Finsupp.mapDomain_apply_of_injective Subtype.val_injective (liftCycle V F p c) ⟨D, hD⟩).trans rfl
  · have hz : c D = 0 := by
      by_contra hn
      exact hD (hc D hn)
    rw [hz]
    exact Finsupp.mapDomain_of_notMem_range (liftCycle V F p c) D (by
      rintro ⟨E, he⟩
      exact hD (he ▸ E.property))

 theorem supportedClass_on_open (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → (D.val : Set V.carrier) ⊆ F)
    (U : Opens V.analyticSpace) :
    Open.SupportedLift.Constructions.Map.relativeClassMap V U {x : U | V.analyticUnderlying x.val ∈ F} p
      (Open.SupportedLift.Constructions.restrictCycle V U {x : U | V.analyticUnderlying x.val ∈ F} p c) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ U (2 * p)
      (Map.Constructions.relativeClassMap V F p (liftCycle V F p c)) := by
  have h := OpenMap.restrictCycle_class_of_global V F p U (liftCycle V F p c)
  rw [forget_liftCycle V F p c hc] at h
  exact h

end AlgebraicGeometry.CycleClass.Thom.Supported.CycleLift.Constructions

end

end OAI
