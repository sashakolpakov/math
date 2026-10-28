import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.CycleSingleThom

/-! # Open Product -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenProduct.Constructions.Class

noncomputable section

/-! On an arbitrary ambient open, restriction of the actual product
cycle class along the actual diagonal is the original supported cup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.CycleSingleThom.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Intersection.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)

def pairedOpenSupport : Set U :=
  (Subtype.val : U → (Ambient.Constructions.productVariety V V).analyticSpace) ⁻¹' Set.range (LocalIsolation.Constructions.pairedSupport V p q A B).analyticInclusion

def pairedOpenInclusion := (Subtype.val : pairedOpenSupport V p q A B U → U)

theorem pairedOpenInclusion_range : Set.range (pairedOpenInclusion V p q A B U) = pairedOpenSupport V p q A B U :=
  Subtype.range_coe

theorem pairedOpenInclusion_closed : IsOpen (Set.range (pairedOpenInclusion V p q A B U))ᶜ := by
  rw [pairedOpenInclusion_range]
  exact ((LocalIsolation.Constructions.pairedSupport V p q A B).isClosedEmbedding_analyticInclusion.isClosed_range.preimage continuous_subtype_val).isOpen_compl

theorem pairedCycle_supported :
    (Subtype.val : U → (Ambient.Constructions.productVariety V V).analyticSpace) ⁻¹'
      Set.range (LocalIsolation.Constructions.pairedSupport V p q A B).analyticInclusion ⊆ Set.range (pairedOpenInclusion V p q A B U) := by
  rw [pairedOpenInclusion_range]
  exact Set.Subset.rfl

local notation "D" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions.diagonalOpenImmersion V U
local notation "W" => OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions.sourceOpen (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions.diagonalImmersion V) U
local notation "u" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenProduct.Constructions.Class.pairedOpenInclusion V p q A B U

theorem diagonalOpen_support :
    (D).regularComplementInclusion ⁻¹' Set.range u =
      (Subtype.val : W → V.analyticSpace) ⁻¹' (Set.range A.analyticInclusion ∩ Set.range B.analyticInclusion) := by
  rw [pairedOpenInclusion_range]
  ext x
  exact Set.ext_iff.mp (SupportedProduct.Constructions.diagonalProduct_support V p q A B) x.val

theorem sourceCup_mapsTo : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (W : Set V.analyticSpace))
    ((D).regularComplementInclusion ⁻¹' (Set.range u)ᶜ)
    (Set.range A.analyticInclusion ∩ Set.range B.analyticInclusion)ᶜ := by
  intro x hx hy
  exact hx ((Set.ext_iff.mp (diagonalOpen_support V p q A B U) x).mpr hy)

theorem diagonalOpen_square :
    (D).regularComplementTopCatMap ≫ Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Ambient.Constructions.productVariety V V).analyticSpace)
      (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) =
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (W : Set V.analyticSpace) ≫ SupportedProduct.Constructions.diagonalPointMap V := rfl

theorem diagonalOpen_productClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (D).regularComplementTopCatMap
      (A := (D).regularComplementInclusion ⁻¹' (Set.range u)ᶜ) (B := (Set.range u)ᶜ)
      (fun _ hx => hx) (2 * (p + q))
      (Open.SupportedLift.Constructions.Map.relativeClassMap (Ambient.Constructions.productVariety V V) U (Set.range u) (p + q)
        (Open.SupportedLift.Constructions.restrictCycle (Ambient.Constructions.productVariety V V) U (Set.range u) (p + q) (Finsupp.single (LocalIsolation.Constructions.pairedSupport V p q A B) 1))) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (W : Set V.analyticSpace))
      (sourceCup_mapsTo V p q A B U) (2 * (p + q)) (Supported.Intersection.Constructions.Class.supportedIntersectionClass A B) := by
  rw [Open.CycleSingleThom.Constructions.relativeClassMap_restrict_single (Ambient.Constructions.productVariety V V) U _ (p + q) (LocalIsolation.Constructions.pairedSupport V p q A B)
    (pairedCycle_supported V p q A B U), one_smul, ← SupportedProduct.Constructions.supportedProduct_diagonal V p q A B]
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (D).regularComplementTopCatMap (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (Ambient.Constructions.productVariety V V).analyticSpace)
      (U : Set (Ambient.Constructions.productVariety V V).analyticSpace))
    (A := (D).regularComplementInclusion ⁻¹' (Set.range u)ᶜ) (B := (Set.range u)ᶜ)
    (fun _ hx => hx)
    (Open.SupportedLift.Constructions.Map.supportComplement_mapsTo (Ambient.Constructions.productVariety V V) U _ (p + q)
      ⟨LocalIsolation.Constructions.pairedSupport V p q A B, pairedCycle_supported V p q A B U⟩) (2 * (p + q))
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (W : Set V.analyticSpace)) (SupportedProduct.Constructions.diagonalPointMap V)
    (sourceCup_mapsTo V p q A B U) (SupportedProduct.Constructions.diagonalProduct_mapsTo V p q A B) (2 * (p + q))
  have he := ThomOpenRestriction.Constructions.pairMap_congr (diagonalOpen_square V U)
    (A := (D).regularComplementInclusion ⁻¹' (Set.range u)ᶜ)
    (B := (Set.range (LocalIsolation.Constructions.pairedSupport V p q A B).analyticInclusion)ᶜ)
    (fun _ hx => Open.SupportedLift.Constructions.Map.supportComplement_mapsTo (Ambient.Constructions.productVariety V V) U _ (p + q)
      ⟨LocalIsolation.Constructions.pairedSupport V p q A B, pairedCycle_supported V p q A B U⟩ hx)
    (fun _ hx => SupportedProduct.Constructions.diagonalProduct_mapsTo V p q A B (sourceCup_mapsTo V p q A B U hx)) (2 * (p + q))
  exact ConcreteCategory.congr_hom (h₁.trans (he.trans h₂.symm)) (LocalIsolation.Constructions.pairedSupport V p q A B).rationalSupportedCycleClass

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenProduct.Constructions.Class
