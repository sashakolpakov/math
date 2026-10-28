import OAI.AlgebraicGeometry.Cycles.Functoriality.CycleProjection
import OAI.AlgebraicGeometry.Cycles.Functoriality.FundamentalDegreeTransport

/-! # Cycle Open Projection -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.CycleOpenProjection.Construction

noncomputable section

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

/-- Compactness is retained on an open subspace containing the whole
compact preimage of the ambient support. -/
theorem isCompact_openRegularPreimage
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    {P : TopCat.{0}} (j : P ⟶ TopCat.of Z.regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j) (L : Compacts V.analyticSpace)
    (hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen)
    (hRange : CycleProjection.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace) ⊆ Set.range j) :
    IsCompact ((j ≫ CycleProjection.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace)) :=
  hj.isEmbedding.isInducing.isCompact_preimage'
    (CycleProjection.Construction.isCompact_regularAmbientMap_preimage Z L hL) hRange

/-- Compact projections of the geometric class can be computed on any
analytic smooth open containing the retained support. -/
theorem geometricCycleFundamentalClass_projection_from_open
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (d : ℕ) {P : Type} [TopologicalSpace P] [T2Space P]
    [ChartedSpace (Fin d → ℂ) P] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 P]
    (j : TopCat.of P ⟶ TopCat.of Z.regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Z.regularAnalyticModel)) ω j)
    (hd : 2 * d = 2 * Z.regularComplexDimension)
    (L : Compacts V.analyticSpace) (hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen)
    (hRange : CycleProjection.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace) ⊆ Set.range j) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ)
      (2 * Z.regularComplexDimension) Z.geometricCycleFundamentalClass =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (j ≫ CycleProjection.Construction.regularAmbientMap Z)
        (A := ((j ≫ CycleProjection.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace))ᶜ)
        (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx)) (2 * Z.regularComplexDimension)
      (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree d
        ((j ≫ CycleProjection.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace))
        (isCompact_openRegularPreimage Z j hj L hL hRange) (2 * Z.regularComplexDimension) hd) := by
  let K := CycleProjection.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace)
  let J := j ⁻¹' K
  have hK : IsCompact K := CycleProjection.Construction.isCompact_regularAmbientMap_preimage Z L hL
  have hJ : IsCompact J := isCompact_openRegularPreimage Z j hj L hL hRange
  have hJK : j '' J = K := Set.image_preimage_eq_of_subset hRange
  have hclass := FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree_injective_toSupport d Z.regularComplexDimension
    j hj.injective hl J hJ K hK hJK (fun _ hx => hx)
    (2 * Z.regularComplexDimension) hd rfl
  have hc := CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ j (CycleProjection.Construction.regularAmbientMap Z)
    (A := Jᶜ) (B := Kᶜ) (C := (L : Set V.analyticSpace)ᶜ)
    (fun _ hx => hx) (fun _ hx => hx) (2 * Z.regularComplexDimension)
  have hc' := ConcreteCategory.congr_hom hc
    (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree d J hJ (2 * Z.regularComplexDimension) hd)
  have hp := CycleProjection.Construction.geometricCycleFundamentalClass_projection Z L hL
  exact hp.trans ((congrArg
    (HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (CycleProjection.Construction.regularAmbientMap Z) (A := Kᶜ)
        (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx)) (2 * Z.regularComplexDimension))
    hclass.symm).trans hc')

/-- The smooth-open projection formula in any equal ambient homology degree. -/
theorem poincareCycleClass_projection_from_open
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (d : ℕ) {P : Type} [TopologicalSpace P] [T2Space P]
    [ChartedSpace (Fin d → ℂ) P] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 P]
    (j : TopCat.of P ⟶ TopCat.of Z.regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Z.regularAnalyticModel)) ω j)
    (L : Compacts V.analyticSpace) (hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen)
    (hRange : CycleProjection.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace) ⊆ Set.range j)
    (n : ℕ) (hd : 2 * d = n) (hZ : 2 * Z.regularComplexDimension = n)
    (hpn : (p + p) + n = 2 * V.complexDimension) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ) n
      ((V.poincareDuality (p + p) n hpn).hom Z.geometricCycleClass) =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (j ≫ CycleProjection.Construction.regularAmbientMap Z)
        (A := ((j ≫ CycleProjection.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace))ᶜ)
        (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree d
        ((j ≫ CycleProjection.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace))
        (isCompact_openRegularPreimage Z j hj L hL hRange) n hd) := by
  cases hZ
  exact geometricCycleFundamentalClass_projection_from_open Z d j hj hl hd L hL hRange

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.CycleOpenProjection.Construction
