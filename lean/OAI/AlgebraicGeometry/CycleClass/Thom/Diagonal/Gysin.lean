import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Inner
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.CycleSingleThom

/-! # Gysin -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Gysin.Constructions

noncomputable section

/-! The genuine supported diagonal Gysin isomorphism sends an actual
single source cycle to its reduced diagonal image, in the same support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.AnalyticImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Inner.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.CycleSingleThom.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComposedEnlargement.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComposedDegree.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.GysinDegree.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
  (hU : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ (Ambient.Constructions.diagonalSupport V p Z).regularAmbientOpen)
  {L : Type} (u : L → U)
  (hZ : (Subtype.val : U → (Ambient.Constructions.productVariety V V).analyticSpace) ⁻¹'
    Set.range (Ambient.Constructions.diagonalSupport V p Z).analyticInclusion ⊆ Set.range u)

local notation "D" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions.diagonalOpenImmersion V U
local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Inner.Constructions.diagonalInnerImmersion V p Z U hU
local notation "W" => OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions.sourceOpen (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions.diagonalImmersion V) U

include hZ in
theorem diagonalSource_supported :
    (Subtype.val : W → V.analyticSpace) ⁻¹' Set.range Z.analyticInclusion ⊆
      (D).regularComplementInclusion ⁻¹' Set.range u := by
  intro x hx
  apply hZ
  rw [AnalyticImage.Constructions.diagonalCycle_range]
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, congrArg (SupportedProduct.Constructions.diagonalPointMap V) hz⟩

include hZ in
theorem diagonalTarget_supported :
    (Subtype.val : U → (Ambient.Constructions.productVariety V V).analyticSpace) ⁻¹'
      Set.range (Ambient.Constructions.diagonalSupport V p Z).analyticInclusion ⊆
      Set.range (D).regularComplementInclusion ∩ Set.range u := by
  intro y hy
  refine ⟨?_, hZ hy⟩
  have h := hy
  rw [AnalyticImage.Constructions.diagonalCycle_range] at h
  obtain ⟨z, hz⟩ := h
  refine ⟨⟨Z.analyticInclusion z, ?_⟩, Subtype.ext hz⟩
  change (SupportedProduct.Constructions.diagonalPointMap V ∘ Z.analyticInclusion) z ∈ U
  rw [hz]
  exact y.property

include hZ in
theorem diagonalComposite_supported :
    Set.range (Inner.Constructions.diagonalCompositeImmersion V p Z U hU).regularComplementInclusion ⊆ Set.range u :=
  fun _ hx => hZ ((Inner.Constructions.diagonalComposite_range V p Z U hU) ▸ hx)

theorem diagonalImageGenerator_compositeThom :
    Open.SupportedLift.Constructions.Map.relativeGenerator (Ambient.Constructions.productVariety V V) U (Set.range (D).regularComplementInclusion ∩ Set.range u)
      (p + V.complexDimension) ⟨Ambient.Constructions.diagonalSupport V p Z, diagonalTarget_supported V p Z U u hZ⟩ =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (ComposedEnlargement.Constructions.targetEnlargement_mapsTo (D) (C) u (diagonalComposite_supported V p Z U hU u hZ))
      (2 * (p + V.complexDimension))
      (ComposedDegree.Constructions.composedThomInDegree (D) (C) (p + V.complexDimension) (Nat.add_comm _ _)) := by
  rw [Open.CycleSingleThom.Constructions.relativeGenerator_eq_Thom (Ambient.Constructions.productVariety V V) U _ (p + V.complexDimension)
    (Ambient.Constructions.diagonalSupport V p Z) (diagonalTarget_supported V p Z U u hZ) hU,
    ← Inner.Constructions.diagonalComposite_Thom V p Z U hU]
  have h := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of U)) (𝟙 (TopCat.of U))
    (Open.CycleSingleThom.Constructions.singleThom_mapsTo (Ambient.Constructions.productVariety V V) U _ (p + V.complexDimension) (Ambient.Constructions.diagonalSupport V p Z)
      (diagonalTarget_supported V p Z U u hZ) hU)
    (ImageInvariant.Constructions.RawThom.imageMapsTo
      (Cycle.RegularOpenImmersion.Constructions.Bundle.cycleOpenImmersion (Ambient.Constructions.diagonalSupport V p Z) U hU).regularComplementInclusion
      (Inner.Constructions.diagonalCompositeImmersion V p Z U hU).regularComplementInclusion
      (Inner.Constructions.diagonalComposite_cycleOpen_range V p Z U hU)) (2 * (p + V.complexDimension)))
      (ComposedDegree.Constructions.composedThomInDegree (D) (C) (p + V.complexDimension) (Nat.add_comm _ _))
  simp only [ConcreteCategory.comp_apply, Category.id_comp] at h
  exact h

variable (hu : IsOpen (Set.range u)ᶜ)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)
    (Set.range (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementInclusion)ᶜ) (2 * V.complexDimension))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * V.complexDimension) a = (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularThomClass)

include hU hZ in
theorem diagonalGysin_singleCycle (r : ℚ) :
    (Intersection.GysinDegree.Constructions.intersectionGysinAt (D) a ha u hu (p + V.complexDimension) (Nat.add_comm _ _)).hom
      (Open.SupportedLift.Constructions.Map.relativeClassMap V W ((D).regularComplementInclusion ⁻¹' Set.range u) p
        (Open.SupportedLift.Constructions.restrictCycle V W ((D).regularComplementInclusion ⁻¹' Set.range u) p (Finsupp.single Z r))) =
    Open.SupportedLift.Constructions.Map.relativeClassMap (Ambient.Constructions.productVariety V V) U (Set.range (D).regularComplementInclusion ∩ Set.range u)
      (p + V.complexDimension)
      (Open.SupportedLift.Constructions.restrictCycle (Ambient.Constructions.productVariety V V) U (Set.range (D).regularComplementInclusion ∩ Set.range u)
        (p + V.complexDimension) (Finsupp.single (Ambient.Constructions.diagonalSupport V p Z) r)) := by
  rw [Open.CycleSingleThom.Constructions.relativeClassMap_restrict_single V W _ p Z (diagonalSource_supported V p Z U u hZ),
    Open.CycleSingleThom.Constructions.relativeClassMap_restrict_single (Ambient.Constructions.productVariety V V) U _ (p + V.complexDimension)
      (Ambient.Constructions.diagonalSupport V p Z) (diagonalTarget_supported V p Z U u hZ), map_smul]
  apply congrArg (fun x => r • x)
  rw [Open.CycleSingleThom.Constructions.relativeGenerator_eq_Thom V W _ p Z (diagonalSource_supported V p Z U u hZ)
      (Inner.Constructions.sourceOpen_regular V p Z U hU),
    diagonalImageGenerator_compositeThom V p Z U hU u hZ]
  exact ComposedDegree.Constructions.gysinAt_enlarged_innerThom (D) (C) (p + V.complexDimension) (Nat.add_comm _ _) u
    (diagonalComposite_supported V p Z U hU u hZ) hu a ha

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Gysin.Constructions
