import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Regular Neighborhood Detection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions

noncomputable section

/-! Original supported cycle-degree classes are determined on
arbitrary ambient neighborhoods of every regular point. Extension
across the actual singular boundary is justified by the proved purity
isomorphism used in the original cycle-class construction. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SheafPurity.Constructions.SupportDetection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

def regularNeighborhood (U : Opens V.analyticSpace) : Opens D.regularAmbientSpace :=
  ⟨Subtype.val ⁻¹' (U : Set V.analyticSpace), U.isOpen.preimage continuous_subtype_val⟩

def regularNeighborhoodMap (U : Opens V.analyticSpace) : TopCat.of (regularNeighborhood D U) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun y => ⟨y.val.val, y.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

theorem regularNeighborhood_mapsTo (U : Opens V.analyticSpace) : Set.MapsTo (regularNeighborhoodMap D U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace) (Set.range D.regularComplementInclusion)ᶜ (regularNeighborhood D U))
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U) :=
  fun y hy => (D.mem_regularThomComplement_iff y.val).mp hy

theorem neighborhood_square (U : Opens V.analyticSpace) :
    D.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p) ≫
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (Set.range D.regularComplementInclusion)ᶜ (regularNeighborhood D U) (2 * p) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range D.analyticInclusion)ᶜ U (2 * p) ≫
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (regularNeighborhoodMap D U)
        (regularNeighborhood_mapsTo D U) (2 * p) := by
  let j := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) D.analyticSingularBoundaryᶜ
  let k := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of D.regularAmbientSpace) (regularNeighborhood D U : Set D.regularAmbientSpace)
  let l := Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace)
  have hj : Set.MapsTo j (Set.range D.regularComplementInclusion)ᶜ (Set.range D.analyticInclusion)ᶜ :=
    fun y hy => (D.mem_regularThomComplement_iff y).mp hy
  have hk : Set.MapsTo k
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace) (Set.range D.regularComplementInclusion)ᶜ (regularNeighborhood D U))
      (Set.range D.regularComplementInclusion)ᶜ := fun _ hy => hy
  have hl : Set.MapsTo l (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace) (Set.range D.analyticInclusion)ᶜ U)
      (Set.range D.analyticInclusion)ᶜ := fun _ hy => hy
  have he : k ≫ j = regularNeighborhoodMap D U ≫ l := by
    ext y
    rfl
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) k j hk hj (2 * p)
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (regularNeighborhoodMap D U) l
    (regularNeighborhood_mapsTo D U) hl (2 * p)
  have hm := ThomOpenRestriction.Constructions.pairMap_congr he (fun _ hy => hj (hk hy))
    (fun _ hy => hl (regularNeighborhood_mapsTo D U hy)) (2 * p)
  exact h₁.trans (hm.trans h₂.symm)

theorem regularPullback_injective : Function.Injective
    (D.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p)) := by
  let e := D.regularToSupportCohomologyIso (ModuleCat.of ℚ ℚ) (2 * p)
    D.singularBoundaryRationalCohomology_two_mul_isZero D.singularBoundaryRationalCohomology_two_mul_add_one_isZero
  have he : e.inv = D.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p) :=
    D.relativeCohomologyTripleRestriction_regularThom (ModuleCat.of ℚ ℚ) (2 * p)
  intro a b hab
  apply (ModuleCat.mono_iff_injective e.inv).mp inferInstance
  rw [he]
  exact hab

theorem relativeClass_eq_of_regular_neighborhoods
    (U : D.regularAnalyticSpace → Opens V.analyticSpace)
    (hU : ∀ x, D.regularAnalyticToAmbient x ∈ U x)
    (a b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range D.analyticInclusion)ᶜ (2 * p))
    (hab : ∀ x, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range D.analyticInclusion)ᶜ (U x) (2 * p) a =
      Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range D.analyticInclusion)ᶜ (U x) (2 * p) b) : a = b := by
  apply regularPullback_injective D
  apply Immersion.SheafPurity.Constructions.SupportDetection.relativeClass_eq_of_neighborhoods (RegularImmersion.Constructions.regularCycleImmersion D) (fun x => regularNeighborhood D (U x))
    (fun x => hU x)
  intro x
  have ha := ConcreteCategory.congr_hom (neighborhood_square D (U x)) a
  have hb := ConcreteCategory.congr_hom (neighborhood_square D (U x)) b
  exact ha.trans ((congrArg (fun c => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (regularNeighborhoodMap D (U x)) (regularNeighborhood_mapsTo D (U x)) (2 * p) c) (hab x)).trans hb.symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularNeighborhoodDetection.Constructions
