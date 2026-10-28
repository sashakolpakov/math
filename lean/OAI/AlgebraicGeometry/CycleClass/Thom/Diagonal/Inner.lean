import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.AnalyticImage
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.ComposedDegree
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageInvariant

/-! # Inner -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Inner.Constructions

noncomputable section

/-! The actual diagonal Thom pushforward of a regular cycle is the
Thom class of its original reduced diagonal image on the same open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.AnalyticImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions.Bundle OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComposedDegree.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageInvariant.Constructions.RawThom OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
  (hU : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ (Ambient.Constructions.diagonalSupport V p Z).regularAmbientOpen)

local instance : IsIntegral V.toOver.left := V.property
local instance : Smooth V.toOver.hom := V.presentation.smooth
local instance : IsIntegral (Ambient.Constructions.productVariety V V).toOver.left := (Ambient.Constructions.productVariety V V).property
local instance : Smooth (Ambient.Constructions.productVariety V V).toOver.hom := (Ambient.Constructions.productVariety V V).presentation.smooth

include hU in
theorem sourceOpen_regular : (Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U : Set V.analyticSpace) ⊆ Z.regularAmbientOpen :=
  fun x hx => AnalyticImage.Constructions.diagonalCycle_regular_preimage V p Z x (hU hx)

abbrev diagonalInnerImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.sourceManifold (ComplexImmersion.Constructions.diagonalOpenImmersion V U)) p :=
  Cycle.RegularOpenImmersion.Constructions.Bundle.cycleOpenImmersion Z (Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U) (sourceOpen_regular V p Z U hU)

abbrev diagonalCompositeImmersion := Open.ClosedImmersionComposition.Constructions.compose (ComplexImmersion.Constructions.diagonalOpenImmersion V U) (diagonalInnerImmersion V p Z U hU)

theorem diagonalComposite_range :
    Set.range (diagonalCompositeImmersion V p Z U hU).regularComplementInclusion =
      (Subtype.val : U → (Ambient.Constructions.productVariety V V).analyticSpace) ⁻¹' Set.range (Ambient.Constructions.diagonalSupport V p Z).analyticInclusion := by
  ext y
  rw [AnalyticImage.Constructions.diagonalCycle_range]
  constructor
  · rintro ⟨x, rfl⟩
    have hx : (diagonalInnerImmersion V p Z U hU).regularComplementInclusion x ∈
        Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion Z (Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U) (sourceOpen_regular V p Z U hU)) :=
      ⟨x, rfl⟩
    rw [Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_range] at hx
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, congrArg (SupportedProduct.Constructions.diagonalPointMap V) hz⟩
  · rintro ⟨z, hz⟩
    let x : Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U := ⟨Z.analyticInclusion z, by
      change (SupportedProduct.Constructions.diagonalPointMap V ∘ Z.analyticInclusion) z ∈ U
      rw [hz]
      exact y.property⟩
    have hx : x ∈ Set.range (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion Z (Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U)
        (sourceOpen_regular V p Z U hU)) := by
      rw [Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_range]
      exact ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hx
    refine ⟨w, Subtype.ext ?_⟩
    exact (congrArg (fun t : Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U => SupportedProduct.Constructions.diagonalPointMap V t.val) hw).trans hz

theorem diagonalComposite_cycleOpen_range :
    Set.range (diagonalCompositeImmersion V p Z U hU).regularComplementInclusion =
      Set.range (Cycle.RegularOpenImmersion.Constructions.Bundle.cycleOpenImmersion (Ambient.Constructions.diagonalSupport V p Z) U hU).regularComplementInclusion :=
  (diagonalComposite_range V p Z U hU).trans (Cycle.RegularOpenImmersion.Constructions.regularOpenImmersion_range (Ambient.Constructions.diagonalSupport V p Z) U hU).symm

theorem diagonalComposite_Thom :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (ImageInvariant.Constructions.RawThom.imageMapsTo (Cycle.RegularOpenImmersion.Constructions.Bundle.cycleOpenImmersion (Ambient.Constructions.diagonalSupport V p Z) U hU).regularComplementInclusion
        (diagonalCompositeImmersion V p Z U hU).regularComplementInclusion
        (diagonalComposite_cycleOpen_range V p Z U hU)) (2 * (p + V.complexDimension))
      (ComposedDegree.Constructions.composedThomInDegree (ComplexImmersion.Constructions.diagonalOpenImmersion V U) (diagonalInnerImmersion V p Z U hU)
        (p + V.complexDimension) (Nat.add_comm _ _)) =
      (Cycle.RegularOpenImmersion.Constructions.Bundle.cycleOpenImmersion (Ambient.Constructions.diagonalSupport V p Z) U hU).regularThomClass := by
  let F := Cycle.RegularOpenImmersion.Constructions.Bundle.cycleOpenImmersion (Ambient.Constructions.diagonalSupport V p Z) U hU
  let G := diagonalCompositeImmersion V p Z U hU
  let := F.chartedSpace
  let := F.manifold
  let := G.chartedSpace
  let := G.manifold
  let M := Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold (SmoothImmersion.Constructions.projectiveManifold (Ambient.Constructions.productVariety V V)) U
  let := M.chartedSpace
  let := M.manifold
  let := M.metrizable
  exact ImageInvariant.Constructions.RawThom.ThomClass_eq_of_image (E := F.regularAnalyticModel) (W := G.regularAnalyticModel)
    F.regularComplementInclusion F.holomorphic F.differential_injective F.closed
    G.regularComplementInclusion G.holomorphic G.differential_injective G.closed
    (p + V.complexDimension) F.regularComplement_complexImmersionCodimension
    (G.regularComplement_complexImmersionCodimension.trans (Nat.add_comm _ _))
    (by
      simp only [Module.finrank_fin_fun]
      have h := G.regularComplexDimension_add_codimension
      change G.regularComplexDimension + (V.complexDimension + p) = (Ambient.Constructions.productVariety V V).complexDimension at h
      omega)
    (diagonalComposite_cycleOpen_range V p Z U hU)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Inner.Constructions
