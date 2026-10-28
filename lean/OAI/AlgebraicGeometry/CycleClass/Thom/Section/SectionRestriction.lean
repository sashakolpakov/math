import OAI.AlgebraicGeometry.CycleClass.Thom.Section.BoundaryRemoval
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.OpenRegularMap

/-! # Section Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.SectionRestriction.Constructions

noncomputable section

/-! The actual relative boundary-removal isomorphism is the literal
presheaf restriction to the retained ambient analytic neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.BoundaryRemoval.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.OpenRegularMap.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0) (U : Opens V.analyticSpace)

local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D B s
local notation "E" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.BoundaryRemoval.Constructions.sectionExceptional D B s hs
local notation "T" => TopCat.of V.analyticSpace
local notation "O" => (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ

def retainedNeighborhood : Opens V.analyticSpace := U ⊓ ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V E

def retainedSwapHomeomorph : retainedNeighborhood D B s hs U ≃ₜ
    ({x : U | V.analyticUnderlying x.val ∈ E}ᶜ : Set U) where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def retainedSwapMap : TopCat.of (retainedNeighborhood D B s hs U) ⟶
    TopCat.of ({x : U | V.analyticUnderlying x.val ∈ E}ᶜ : Set U) :=
  TopCat.ofHom ⟨retainedSwapHomeomorph D B s hs U, (retainedSwapHomeomorph D B s hs U).continuous⟩

theorem retainedSwap_mapsTo : Set.MapsTo (retainedSwapMap D B s hs U)
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O (retainedNeighborhood D B s hs U))
    (Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of U) {x : U | V.analyticUnderlying x.val ∈ E}ᶜ
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O U)) := fun _ hx => hx

def retainedSwapCohomologyIso (n : ℕ) := AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity.relativePairHomeomorphCohomologyIso (ModuleCat.of ℚ ℚ)
  (X := TopCat.of (retainedNeighborhood D B s hs U))
  (Y := TopCat.of ({x : U | V.analyticUnderlying x.val ∈ E}ᶜ : Set U))
  (retainedSwapHomeomorph D B s hs U)
  (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O (retainedNeighborhood D B s hs U))
  (Geometric.RelativeCochainTriple.Cohomology.relativeTripleSubspace (TopCat.of U) {x : U | V.analyticUnderlying x.val ∈ E}ᶜ
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O U)) (fun _ => Iff.rfl) n

theorem retainedRestriction_factor (n : ℕ) :
    Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | V.analyticUnderlying x.val ∈ E}ᶜ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O U) n ≫
        (retainedSwapCohomologyIso D B s hs U n).hom =
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) T O n).map
      (homOfLE (show retainedNeighborhood D B s hs U ≤ U from inf_le_left)).op := by
  have hh : (retainedSwapCohomologyIso D B s hs U n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (retainedSwapMap D B s hs U)
        (retainedSwap_mapsTo D B s hs U) n := rfl
  rw [hh]
  exact Cycle.OpenRegularMap.Constructions.triple_pairMap (X := TopCat.of U) (Y := TopCat.of (retainedNeighborhood D B s hs U))
    ({x : U | V.analyticUnderlying x.val ∈ E}ᶜ : Set U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O U)
    (retainedSwapMap D B s hs U) (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O (retainedNeighborhood D B s hs U))
    (retainedSwap_mapsTo D B s hs U) n

theorem retainedRestriction_injective :
    Function.Injective ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) T O (2 * (Geometric.DimensionCycles.dimensionCodimension V D.val + 1))).map
      (homOfLE (show retainedNeighborhood D B s hs U ≤ U from inf_le_left)).op) := by
  let : IsIso (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | V.analyticUnderlying x.val ∈ E}ᶜ (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := T) O U)
      (2 * (Geometric.DimensionCycles.dimensionCodimension V D.val + 1))) := BoundaryRemoval.Constructions.section_relativeRestriction_isIso D B s hs U
  have : IsIso ((AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheaf (ModuleCat.of ℚ ℚ) T O (2 * (Geometric.DimensionCycles.dimensionCodimension V D.val + 1))).map
      (homOfLE (show retainedNeighborhood D B s hs U ≤ U from inf_le_left)).op) := by
    rw [← retainedRestriction_factor]
    infer_instance
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.SectionRestriction.Constructions
