import OAI.AlgebraicGeometry.Cycles.Functoriality.CycleSupport
import OAI.AlgebraicGeometry.Cycles.Functoriality.RationalCompactFundamental

/-! # Cycle Projection -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.CycleProjection.Construction

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

/-- Rewriting the retained compact source set does not alter its
relative fundamental-class pushforward. -/
theorem rationalCompactFundamentalClass_map_support_congr
    (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    {Y : TopCat.{0}} (f : TopCat.of M ⟶ Y)
    {K L : Set M} (h : K = L) (hK : IsCompact K) (hL : IsCompact L)
    (B : Set Y) (hfK : Set.MapsTo f Kᶜ B) (hfL : Set.MapsTo f Lᶜ B) :
    HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hfK) (2 * d)
      (RationalCompactFundamental.Construction.rationalCompactFundamentalClass d K hK) =
    HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hfL) (2 * d)
      (RationalCompactFundamental.Construction.rationalCompactFundamentalClass d L hL) := by
  subst L
  rfl

/-- The regular locus's genuine continuous map into the compact ambient variety. -/
def regularAmbientMap {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) : TopCat.of Z.regularAnalyticSpace ⟶ TopCat.of V.analyticSpace :=
  Z.regularComplementTopCatMap ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace)
    (Z.regularAmbientOpen : Set V.analyticSpace)

theorem regularAmbientMap_apply {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (x : Z.regularAnalyticSpace) :
    regularAmbientMap Z x = Z.regularAnalyticToAmbient x := rfl

/-- The regular-locus preimage of a compact ambient set avoiding the
singular boundary is compact. -/
theorem isCompact_regularAmbientMap_preimage
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (L : Compacts V.analyticSpace) (hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen) :
    IsCompact (regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace)) := by
  let K : Compacts Z.regularAmbientSpace :=
    (AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso Z.regularAmbientOpen).symm ⟨L, hL⟩
  exact Z.isCompact_regularCompactPreimage (K : Set Z.regularAmbientSpace) K.isCompact

/-- The projection at the image of an open compact support is the
relative pushforward of the regular fundamental class. -/
theorem geometricCycleFundamentalClass_projection_openSupport
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (K : Compacts Z.regularAmbientSpace) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace)
        (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of V.analyticSpace) Z.regularAmbientOpen K : Set V.analyticSpace)ᶜ)
      (2 * Z.regularComplexDimension) Z.geometricCycleFundamentalClass =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (regularAmbientMap Z)
        (A := (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))ᶜ)
        (B := (AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of V.analyticSpace) Z.regularAmbientOpen K : Set V.analyticSpace)ᶜ)
        (by
          intro x hx hy
          obtain ⟨z, hz, he⟩ := hy
          apply hx
          change Z.regularComplementTopCatMap x ∈ (K : Set Z.regularAmbientSpace)
          exact (Subtype.ext he) ▸ hz)) (2 * Z.regularComplexDimension)
      (RationalCompactFundamental.Construction.rationalCompactFundamentalClass Z.regularComplexDimension
        (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))
        (Z.isCompact_regularCompactPreimage (K : Set Z.regularAmbientSpace) K.isCompact)) := by
  let U := Z.regularAmbientOpen
  let L := AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of V.analyticSpace) U K
  let j : TopCat.of Z.regularAmbientSpace ⟶ TopCat.of V.analyticSpace :=
    CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (U : Set V.analyticSpace)
  have hj : Set.MapsTo j (K : Set Z.regularAmbientSpace)ᶜ (L : Set V.analyticSpace)ᶜ := by
    rintro x hx ⟨z, hz, he⟩
    exact hx ((Subtype.ext he) ▸ hz)
  have hp := ConcreteCategory.congr_hom
    (CompactProjection.Construction.openCompactRelativeTrace_projection (X := TopCat.of V.analyticSpace) U K
      (2 * Z.regularComplexDimension)) Z.geometricCycleFundamentalClass
  have ht := Z.geometricCycleFundamentalClass_compactTrace_integralPushforward K
  have he : (CompactProjection.Construction.openCompactHomologyIso (X := TopCat.of V.analyticSpace) U K
      (2 * Z.regularComplexDimension)).hom =
    HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ j hj)
      (2 * Z.regularComplexDimension) :=
    CompactProjection.Construction.openCompactHomologyIso_hom (X := TopCat.of V.analyticSpace) U K (2 * Z.regularComplexDimension)
  have hc := CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ Z.regularComplementTopCatMap j
    (A := (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))ᶜ)
    (B := (K : Set Z.regularAmbientSpace)ᶜ) (C := (L : Set V.analyticSpace)ᶜ)
    (fun _ hx => hx) hj (2 * Z.regularComplexDimension)
  change (CompactProjection.Construction.openCompactHomologyIso (X := TopCat.of V.analyticSpace) U K
    (2 * Z.regularComplexDimension)).hom
    (Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension)
      Z.geometricCycleFundamentalClass) = _ at hp
  rw [he] at hp
  exact hp.symm.trans ((congrArg
    (HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ j hj)
      (2 * Z.regularComplexDimension)) ht).trans
    (ConcreteCategory.congr_hom hc
      (RationalCompactFundamental.Construction.rationalCompactFundamentalClass Z.regularComplexDimension
        (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))
        (Z.isCompact_regularCompactPreimage (K : Set Z.regularAmbientSpace) K.isCompact))))

/-- An ambient compact projection of the geometric class is the literal
relative pushforward of the regular locus's compact fundamental class. -/
theorem geometricCycleFundamentalClass_projection
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (L : Compacts V.analyticSpace) (hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ)
      (2 * Z.regularComplexDimension) Z.geometricCycleFundamentalClass =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (regularAmbientMap Z)
        (A := (regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace))ᶜ)
        (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx)) (2 * Z.regularComplexDimension)
      (RationalCompactFundamental.Construction.rationalCompactFundamentalClass Z.regularComplexDimension
        (regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace))
        (isCompact_regularAmbientMap_preimage Z L hL)) := by
  let K : Compacts Z.regularAmbientSpace :=
    (AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso Z.regularAmbientOpen).symm ⟨L, hL⟩
  have himage : AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of V.analyticSpace) Z.regularAmbientOpen K = L :=
    congrArg Subtype.val ((AlgebraicTopology.Duality.Poincare.CompactOpenIndex.openCompactsOrderIso Z.regularAmbientOpen).apply_symm_apply ⟨L, hL⟩)
  have h := geometricCycleFundamentalClass_projection_openSupport Z K
  let L' := AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage (X := TopCat.of V.analyticSpace) Z.regularAmbientOpen K
  have hL' : (L' : Set V.analyticSpace) ⊆ Z.regularAmbientOpen :=
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.openSupportImage_subset (X := TopCat.of V.analyticSpace) Z.regularAmbientOpen K
  have hpre : Z.regularCompactPreimage (K : Set Z.regularAmbientSpace) =
      regularAmbientMap Z ⁻¹' (L' : Set V.analyticSpace) := by
    ext x
    constructor
    · intro hx
      exact ⟨Z.regularComplementTopCatMap x, hx, rfl⟩
    · rintro ⟨z, hz, he⟩
      change Z.regularComplementTopCatMap x ∈ (K : Set Z.regularAmbientSpace)
      exact (Subtype.ext he) ▸ hz
  have hs := rationalCompactFundamentalClass_map_support_congr Z.regularComplexDimension
    (regularAmbientMap Z) hpre
    (Z.isCompact_regularCompactPreimage (K : Set Z.regularAmbientSpace) K.isCompact)
    (isCompact_regularAmbientMap_preimage Z L' hL') (L' : Set V.analyticSpace)ᶜ
    (by
      intro x hx hy
      exact hx (hpre.symm ▸ hy)) (fun _ hx => hx)
  have hfull := h.trans hs
  change L' = L at himage
  let P : Compacts V.analyticSpace → Prop := fun C =>
    ∀ hC : (C : Set V.analyticSpace) ⊆ Z.regularAmbientOpen,
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (C : Set V.analyticSpace)ᶜ)
      (2 * Z.regularComplexDimension) Z.geometricCycleFundamentalClass =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (regularAmbientMap Z)
        (A := (regularAmbientMap Z ⁻¹' (C : Set V.analyticSpace))ᶜ)
        (B := (C : Set V.analyticSpace)ᶜ) (fun _ hx => hx)) (2 * Z.regularComplexDimension)
      (RationalCompactFundamental.Construction.rationalCompactFundamentalClass Z.regularComplexDimension
        (regularAmbientMap Z ⁻¹' (C : Set V.analyticSpace))
        (isCompact_regularAmbientMap_preimage Z C hC))
  have hP : P L' := fun _ => hfull
  exact (Eq.mp (congrArg P himage) hP) hL

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.CycleProjection.Construction
