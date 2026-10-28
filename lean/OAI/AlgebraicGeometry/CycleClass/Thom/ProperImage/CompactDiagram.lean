import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Projection
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.FundamentalDegreeTransport

/-! # Compact Diagram -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.CompactDiagram.Constructions.Construction

noncomputable section

section

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

/-- Compactness is retained on an open subspace containing the whole
compact preimage of the ambient support. -/
theorem isCompact_openRegularPreimage
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
    {P : TopCat.{0}} (j : P ⟶ TopCat.of Z.regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j) (L : Compacts V.analyticSpace)
    (hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen)
    (hRange : Projection.Constructions.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace) ⊆ Set.range j) :
    IsCompact ((j ≫ Projection.Constructions.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace)) :=
  hj.isEmbedding.isInducing.isCompact_preimage'
    (Projection.Constructions.Construction.isCompact_regularAmbientMap_preimage Z L hL) hRange

/-- Compact projections of the geometric class can be computed on any
analytic smooth open containing the retained support. -/
theorem geometricCycleFundamentalClass_projection_from_open
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
    (d : ℕ) {P : Type} [TopologicalSpace P] [T2Space P]
    [ChartedSpace (Fin d → ℂ) P] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 P]
    (j : TopCat.of P ⟶ TopCat.of Z.regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Z.regularAnalyticModel)) ω j)
    (hd : 2 * d = 2 * Z.regularComplexDimension)
    (L : Compacts V.analyticSpace) (hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen)
    (hRange : Projection.Constructions.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace) ⊆ Set.range j) :
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ)
      (2 * Z.regularComplexDimension) Z.geometricCycleFundamentalClass =
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (j ≫ Projection.Constructions.Construction.regularAmbientMap Z)
        (A := ((j ≫ Projection.Constructions.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace))ᶜ)
        (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx)) (2 * Z.regularComplexDimension)
      (FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d
        ((j ≫ Projection.Constructions.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace))
        (isCompact_openRegularPreimage Z j hj L hL hRange) (2 * Z.regularComplexDimension) hd) := by
  let K := Projection.Constructions.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace)
  let J := j ⁻¹' K
  have hK : IsCompact K := Projection.Constructions.Construction.isCompact_regularAmbientMap_preimage Z L hL
  have hJ : IsCompact J := isCompact_openRegularPreimage Z j hj L hL hRange
  have hJK : j '' J = K := Set.image_preimage_eq_of_subset hRange
  have hclass := FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree_injective_toSupport d Z.regularComplexDimension
    j hj.injective hl J hJ K hK hJK (fun _ hx => hx)
    (2 * Z.regularComplexDimension) hd rfl
  have hc := Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ j (Projection.Constructions.Construction.regularAmbientMap Z)
    (A := Jᶜ) (B := Kᶜ) (C := (L : Set V.analyticSpace)ᶜ)
    (fun _ hx => hx) (fun _ hx => hx) (2 * Z.regularComplexDimension)
  have hc' := ConcreteCategory.congr_hom hc
    (FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d J hJ (2 * Z.regularComplexDimension) hd)
  have hp := Projection.Constructions.Construction.geometricCycleFundamentalClass_projection Z L hL
  exact hp.trans ((congrArg
    (HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (Projection.Constructions.Construction.regularAmbientMap Z) (A := Kᶜ)
        (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx)) (2 * Z.regularComplexDimension))
    hclass.symm).trans hc')

/-- The smooth-open projection formula in any equal ambient homology degree. -/
theorem poincareCycleClass_projection_from_open
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
    (d : ℕ) {P : Type} [TopologicalSpace P] [T2Space P]
    [ChartedSpace (Fin d → ℂ) P] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 P]
    (j : TopCat.of P ⟶ TopCat.of Z.regularAnalyticSpace)
    (hj : Topology.IsOpenEmbedding j)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Z.regularAnalyticModel)) ω j)
    (L : Compacts V.analyticSpace) (hL : (L : Set V.analyticSpace) ⊆ Z.regularAmbientOpen)
    (hRange : Projection.Constructions.Construction.regularAmbientMap Z ⁻¹' (L : Set V.analyticSpace) ⊆ Set.range j)
    (n : ℕ) (hd : 2 * d = n) (hZ : 2 * Z.regularComplexDimension = n)
    (hpn : (p + p) + n = 2 * V.complexDimension) :
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ) n
      ((V.poincareDuality (p + p) n hpn).hom Z.geometricCycleClass) =
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (j ≫ Projection.Constructions.Construction.regularAmbientMap Z)
        (A := ((j ≫ Projection.Constructions.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace))ᶜ)
        (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d
        ((j ≫ Projection.Constructions.Construction.regularAmbientMap Z) ⁻¹' (L : Set V.analyticSpace))
        (isCompact_openRegularPreimage Z j hj L hL hRange) n hd) := by
  cases hZ
  exact geometricCycleFundamentalClass_projection_from_open Z d j hj hl hd L hL hRange

end

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

/-- Equal continuous maps have equal compact fundamental-class
pushforwards, including the induced equality of their retained source sets. -/
theorem rationalCompactFundamentalClassInDegree_push_congr
    (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    {Y : TopCat.{0}} (f g : TopCat.of M ⟶ Y) (h : f = g) (K : Set Y)
    (hf : IsCompact (f ⁻¹' K)) (hg : IsCompact (g ⁻¹' K))
    (n : ℕ) (hn : 2 * d = n) :
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d (f ⁻¹' K) hf n hn) =
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ g (A := (g ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d (g ⁻¹' K) hg n hn) := by
  subst g
  rfl

/-- Composing a compact fundamental-class pushforward with a finite
covering multiplies it by the covering degree. -/
theorem rationalCompactFundamentalClassInDegree_comp_degree
    (d e : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin e → ℂ)) 1 N]
    {Y : TopCat.{0}} (h : TopCat.of M ⟶ TopCat.of N) (hp : IsProperMap h)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin e → ℂ)) ω h)
    (degree : ℕ) (hdegree : ∀ y : N, Nat.card (h ⁻¹' {y}) = degree)
    (g : TopCat.of N ⟶ Y) (K : Set Y) (hK : IsCompact (g ⁻¹' K))
    (n : ℕ) (hd : 2 * d = n) (he : 2 * e = n) :
    HomologicalComplex.homologyMap
      (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (h ≫ g) (A := ((h ≫ g) ⁻¹' K)ᶜ) (B := Kᶜ)
        (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d ((h ≫ g) ⁻¹' K)
        (hp.isCompact_preimage hK) n hd) =
    (degree : ℚ) •
      HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ g (A := (g ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
        (FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree e (g ⁻¹' K) hK n he) := by
  have hfund := FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree_map_degree d e h hp hl degree hdegree
    (g ⁻¹' K) hK n hd he
  have hc := ConcreteCategory.congr_hom
    (Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ h g (A := ((h ≫ g) ⁻¹' K)ᶜ)
      (B := (g ⁻¹' K)ᶜ) (C := Kᶜ) (fun _ hx => hx) (fun _ hx => hx) n)
    (FundamentalDegreeTransport.Constructions.Construction.rationalCompactFundamentalClassInDegree d ((h ≫ g) ⁻¹' K) (hp.isCompact_preimage hK) n hd)
  let r := HomologicalComplex.homologyMap
    (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ g (A := (g ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
  exact hc.symm.trans ((congrArg r hfund).trans (r.hom.map_smul _ _))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.CompactDiagram.Constructions.Construction
