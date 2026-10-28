import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum

/-! # Analytic Restriction -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction

/-! On an open isolating one algebraic support, a supported cycle class
is precisely its original coefficient times that support's class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (F : Closeds V.carrier) (p : ℕ)
local notation "T" => TopCat.of V.analyticSpace
local notation "O" => (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ

theorem relativeGenerator_restrict_away (Z : Map.Constructions.SupportedSupport V F p)
    (U : V.carrier.Opens) (hU : (U : Set V.carrier) ⊆ (Z.val.val : Set V.carrier)ᶜ) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver U) (2 * p)
      (Map.Constructions.relativeGenerator V F p Z) = 0 := by
  let f := Geometric.LocalHomology.Cycles.subspaceInclusion T (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver U : Set T)
  let ha : Set.MapsTo f (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver U)) O := by
    intro x hx
    exact hx
  have hr : ∀ x, f x ∈ (Set.range Z.val.analyticInclusion)ᶜ := by
    intro x
    rw [Z.val.range_analyticInclusion]
    exact hU x.property
  have hz := DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset (ModuleCat.of ℚ ℚ) f
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver U)) (Set.range Z.val.analyticInclusion)ᶜ
    (fun _ hx => Map.Constructions.supportComplement_subset V F p Z (ha hx)) hr (2 * p)
  have hc : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 T)
      (Map.Constructions.supportComplement_subset V F p Z) (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f ha (2 * p) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f
        (fun _ hx => Map.Constructions.supportComplement_subset V F p Z (ha hx)) (2 * p) := by
    simpa only [Category.comp_id] using AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp
      (ModuleCat.of ℚ ℚ) f (𝟙 T) ha (Map.Constructions.supportComplement_subset V F p Z) (2 * p)
  have hv := ConcreteCategory.congr_hom hc Z.val.rationalSupportedCycleClass
  rw [hz] at hv
  exact hv

theorem relativeClassMap_restrict_isolated (d : Map.Constructions.SupportedCycle V F p)
    (Z : Map.Constructions.SupportedSupport V F p) (U : V.carrier.Opens)
    (hU : ∀ W : Map.Constructions.SupportedSupport V F p, W ≠ Z →
      (U : Set V.carrier) ⊆ (W.val.val : Set V.carrier)ᶜ) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver U) (2 * p)
      (Map.Constructions.relativeClassMap V F p d) =
      d Z • Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) T O
        (Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver U) (2 * p) (Map.Constructions.relativeGenerator V F p Z) := by
  classical
  simp only [Map.Constructions.relativeClassMap, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  rw [Finset.sum_eq_single Z]
  · exact map_smul _ _ _
  · intro W _ hW
    rw [map_smul, relativeGenerator_restrict_away V F p W U (hU W hW), smul_zero]
  · intro hZ
    rw [Finsupp.notMem_support_iff.mp hZ, zero_smul, map_zero]

end Constructions

end AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction

namespace AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction.Constructions

/-! An actual finite supported cycle restricts near an isolated
component to its original coefficient times that component's class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pairMap_targetSupportCast {X Y : TopCat} (f : X ⟶ Y) {A : Set X} {B B' : Set Y}
    (he : B = B') (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A B') (d : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y B d) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf' d
      (eqToHom (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) Y S d) he) a) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf d a := by
  cases he
  rfl

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (F : Closeds V.carrier) (p : ℕ)
  (P : Opens V.analyticSpace) (S : Set P)
  (hF : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace)) S
    (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ)

theorem relativeGenerator_pullback (Z : Map.Constructions.SupportedSupport V F p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace)) hF (2 * p)
      (Map.Constructions.relativeGenerator V F p Z) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace))
      (fun _ hx => Map.Constructions.supportComplement_subset V F p Z (hF hx)) (2 * p) Z.val.rationalSupportedCycleClass := by
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace)) (𝟙 (TopCat.of V.analyticSpace))
    hF (Map.Constructions.supportComplement_subset V F p Z) (2 * p)) Z.val.rationalSupportedCycleClass
  simp only [ConcreteCategory.comp_apply, Category.comp_id] at h
  exact h

theorem relativeGenerator_pullback_zero (Z : Map.Constructions.SupportedSupport V F p)
    (hZ : ∀ x : P, x.val ∉ Set.range Z.val.analyticInclusion) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace)) hF (2 * p)
      (Map.Constructions.relativeGenerator V F p Z) = 0 := by
  rw [relativeGenerator_pullback]
  exact ConcreteCategory.congr_hom (DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace)) S
    (Set.range Z.val.analyticInclusion)ᶜ (fun _ hx => Map.Constructions.supportComplement_subset V F p Z (hF hx)) hZ (2 * p))
      Z.val.rationalSupportedCycleClass

theorem relativeClassMap_pullback_isolated (c : Map.Constructions.SupportedCycle V F p) (Z : Map.Constructions.SupportedSupport V F p)
    (hZ : ∀ W : Map.Constructions.SupportedSupport V F p, W ≠ Z → ∀ x : P, x.val ∉ Set.range W.val.analyticInclusion) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace)) hF (2 * p)
      (Map.Constructions.relativeClassMap V F p c) =
    c Z • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace))
      (fun _ hx => Map.Constructions.supportComplement_subset V F p Z (hF hx)) (2 * p) Z.val.rationalSupportedCycleClass := by
  classical
  simp only [Map.Constructions.relativeClassMap, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  rw [Finset.sum_eq_single Z]
  · rw [map_smul, relativeGenerator_pullback]
  · intro W _ hW
    rw [map_smul, relativeGenerator_pullback_zero V F p P S hF W (hZ W hW), smul_zero]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, zero_smul, map_zero]

end AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction.Constructions

end

end OAI
