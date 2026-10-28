import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction

/-! # Supported Lift -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map

/-! Actual finite cycle classes in a fixed support on an analytic open.
Their equality can be checked on the original coefficients of the
supports that meet that open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (U : Opens V.analyticSpace) (S : Set U) (p : ℕ)

abbrev SupportedSupport := {D : Geometric.DimensionCycles.DimensionCycleSupport V p //
  (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S}
abbrev SupportedCycle := SupportedSupport V U S p →₀ ℚ

def forgetCycle : SupportedCycle V U S p →ₗ[ℚ] Geometric.DimensionCycles.RationalDimensionCycle V p :=
  Finsupp.lmapDomain ℚ ℚ (fun D : SupportedSupport V U S p => D.val)

theorem forgetCycle_apply (c : SupportedCycle V U S p) (D : SupportedSupport V U S p) :
    forgetCycle V U S p c D.val = c D :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective c D

theorem supportComplement_mapsTo (D : SupportedSupport V U S p) :
    Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
      Sᶜ (Set.range D.val.analyticInclusion)ᶜ := fun _ hx hy => hx (D.property hy)

def relativeGenerator (D : SupportedSupport V U S p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Sᶜ (2 * p) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace))
    (supportComplement_mapsTo V U S p D) (2 * p) D.val.rationalSupportedCycleClass

def relativeClassMap : SupportedCycle V U S p →ₗ[ℚ]
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) Sᶜ (2 * p) :=
  Finsupp.linearCombination ℚ (relativeGenerator V U S p)

theorem relativeClassMap_single (D : SupportedSupport V U S p) (r : ℚ) :
    relativeClassMap V U S p (Finsupp.single D r) = r • relativeGenerator V U S p D :=
  Finsupp.linearCombination_single ℚ r D

theorem relativeGenerator_zero_of_disjoint (D : SupportedSupport V U S p)
    (hD : ∀ x : U, x.val ∉ Set.range D.val.analyticInclusion) :
    relativeGenerator V U S p D = 0 := by
  have h := DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace)) Sᶜ
    (Set.range D.val.analyticInclusion)ᶜ (supportComplement_mapsTo V U S p D) hD (2 * p)
  exact ConcreteCategory.congr_hom h D.val.rationalSupportedCycleClass

theorem relativeClassMap_eq_of_local_coefficients (c e : SupportedCycle V U S p)
    (h : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, (∃ x : U, x.val ∈ Set.range D.analyticInclusion) →
      forgetCycle V U S p c D = forgetCycle V U S p e D) :
    relativeClassMap V U S p c = relativeClassMap V U S p e := by
  classical
  apply sub_eq_zero.mp
  rw [← map_sub, relativeClassMap, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro D _
  by_cases hD : ∃ x : U, x.val ∈ Set.range D.val.analyticInclusion
  · have hc := h D.val hD
    rw [forgetCycle_apply, forgetCycle_apply] at hc
    rw [Finsupp.sub_apply, hc, sub_self, zero_smul]
  · have hz := relativeGenerator_zero_of_disjoint V U S p D (by simpa only [not_exists] using hD)
    rw [hz, smul_zero]

end AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map

namespace AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions

/-! A genuine finite cycle whose retained supports lie in a prescribed
analytic support has a canonical lift to the supported cycle module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (U : Opens V.analyticSpace) (S : Set U) (p : ℕ)

def restrictCycle (c : Geometric.DimensionCycles.RationalDimensionCycle V p) : Map.SupportedCycle V U S p :=
  Finsupp.subtypeDomain (fun D : Geometric.DimensionCycles.DimensionCycleSupport V p =>
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S) c

theorem restrictCycle_apply (c : Geometric.DimensionCycles.RationalDimensionCycle V p) (D : Map.SupportedSupport V U S p) :
    restrictCycle V U S p c D = c D.val := rfl

theorem forget_restrictCycle (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S) :
    Map.forgetCycle V U S p (restrictCycle V U S p c) = c := by
  classical
  ext D
  by_cases hD : (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S
  · exact (Map.forgetCycle_apply V U S p (restrictCycle V U S p c) ⟨D, hD⟩).trans rfl
  · have hz : c D = 0 := by
      by_contra hn
      exact hD (hc D hn)
    rw [hz]
    exact Finsupp.mapDomain_of_notMem_range (restrictCycle V U S p c) D (by
      rintro ⟨E, he⟩
      exact hD (he ▸ E.property))

theorem supportedClass_eq_of_local_coefficients (c e : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S)
    (he : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, e D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S)
    (hcoeff : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, (∃ x : U, x.val ∈ Set.range D.analyticInclusion) → c D = e D) :
    Map.relativeClassMap V U S p (restrictCycle V U S p c) =
      Map.relativeClassMap V U S p (restrictCycle V U S p e) := by
  apply Map.relativeClassMap_eq_of_local_coefficients
  intro D hD
  rw [forget_restrictCycle V U S p c hc, forget_restrictCycle V U S p e he]
  exact hcoeff D hD

theorem forgetCycle_supported (c : Map.SupportedCycle V U S p) (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
    (hc : Map.forgetCycle V U S p c D ≠ 0) :
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S := by
  have hr : D ∈ Set.range (fun E : Map.SupportedSupport V U S p => E.val) :=
    Finsupp.mem_range_of_mapDomain_ne_zero hc
  obtain ⟨E, hE⟩ := hr
  exact hE ▸ E.property

theorem supports_of_local_coefficients (c : Map.SupportedCycle V U S p) (e : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hcoeff : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, (∃ x : U, x.val ∈ Set.range D.analyticInclusion) →
      Map.forgetCycle V U S p c D = e D) :
    ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, e D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S := by
  intro D hD x hx
  have hc : Map.forgetCycle V U S p c D ≠ 0 := by
    rw [hcoeff D ⟨x, hx⟩]
    exact hD
  exact forgetCycle_supported V U S p c D hc hx

theorem relativeClassMap_eq_restrict_of_local_coefficients
    (c : Map.SupportedCycle V U S p) (e : Geometric.DimensionCycles.RationalDimensionCycle V p)
    (hcoeff : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, (∃ x : U, x.val ∈ Set.range D.analyticInclusion) →
      Map.forgetCycle V U S p c D = e D) :
    Map.relativeClassMap V U S p c = Map.relativeClassMap V U S p (restrictCycle V U S p e) := by
  apply Map.relativeClassMap_eq_of_local_coefficients
  intro D hD
  rw [forget_restrictCycle V U S p e (supports_of_local_coefficients V U S p c e hcoeff)]
  exact hcoeff D hD

end AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions

end

end OAI
