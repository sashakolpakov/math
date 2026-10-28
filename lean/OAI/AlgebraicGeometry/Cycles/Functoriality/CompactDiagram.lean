import OAI.AlgebraicGeometry.Cycles.Functoriality.CycleOpenProjection

/-! # Compact Diagram -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.CompactDiagram.Construction

noncomputable section

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
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree d (f ⁻¹' K) hf n hn) =
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ g (A := (g ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree d (g ⁻¹' K) hg n hn) := by
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
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (h ≫ g) (A := ((h ≫ g) ⁻¹' K)ᶜ) (B := Kᶜ)
        (fun _ hx => hx)) n
      (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree d ((h ≫ g) ⁻¹' K)
        (hp.isCompact_preimage hK) n hd) =
    (degree : ℚ) •
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ g (A := (g ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
        (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree e (g ⁻¹' K) hK n he) := by
  have hfund := FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree_map_degree d e h hp hl degree hdegree
    (g ⁻¹' K) hK n hd he
  have hc := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ h g (A := ((h ≫ g) ⁻¹' K)ᶜ)
      (B := (g ⁻¹' K)ᶜ) (C := Kᶜ) (fun _ hx => hx) (fun _ hx => hx) n)
    (FundamentalDegreeTransport.Construction.rationalCompactFundamentalClassInDegree d ((h ≫ g) ⁻¹' K) (hp.isCompact_preimage hK) n hd)
  let r := HomologicalComplex.homologyMap
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ g (A := (g ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
  exact hc.symm.trans ((congrArg r hfund).trans (r.hom.map_smul _ _))

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.CompactDiagram.Construction
