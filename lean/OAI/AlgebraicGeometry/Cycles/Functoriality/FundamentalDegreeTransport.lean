import OAI.AlgebraicGeometry.Cycles.Functoriality.LocalOrientation
import OAI.AlgebraicGeometry.Cycles.Functoriality.RationalCompactFundamental

/-! # Fundamental Degree Transport -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.FundamentalDegreeTransport.Construction

noncomputable section

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

/-- The genuine rational compact fundamental class in any equal degree. -/
def rationalCompactFundamentalClassInDegree
    (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    (K : Set M) (hK : IsCompact K) (n : ℕ) (hn : 2 * d = n) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of M) Kᶜ n :=
  (eqToHom (congrArg (fun k => CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of M) Kᶜ k) hn))
    (RationalCompactFundamental.Construction.rationalCompactFundamentalClass d K hK)

/-- An analytic open embedding preserves the rational compact class
with source and target dimensions written independently. -/
theorem rationalCompactFundamentalClassInDegree_injective_localDiffeomorph
    (d e : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N]
    [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin e → ℂ)) 1 N]
    (f : TopCat.of M ⟶ TopCat.of N) (hf : Function.Injective f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin e → ℂ)) ω f)
    (K : Set M) (hK : IsCompact K) (n : ℕ) (hd : 2 * d = n) (he : 2 * e = n) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f ((Set.surjOn_image f K).mapsTo_compl hf)) n
      (rationalCompactFundamentalClassInDegree d K hK n hd) =
    rationalCompactFundamentalClassInDegree e (f '' K) (hK.image f.hom.continuous) n he := by
  have hde : e = d := by omega
  subst e
  subst n
  change HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f ((Set.surjOn_image f K).mapsTo_compl hf)) (2 * d)
      (RationalCompactFundamental.Construction.rationalCompactFundamentalClass d K hK) =
    RationalCompactFundamental.Construction.rationalCompactFundamentalClass d (f '' K) (hK.image f.hom.continuous)
  exact (RationalCompactFundamental.Construction.rationalizeRelativeClass_naturality f _ (2 * d)
    (CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d K hK)).trans
    (congrArg (RationalCompactFundamental.Construction.rationalizeRelativeClass (TopCat.of N) (f '' K)ᶜ (2 * d))
      (LocalOrientation.Construction.complexCompactFundamentalClass_injective_localDiffeomorph d f hf hl K hK))

/-- The same open-embedding formula with an explicitly specified image support. -/
theorem rationalCompactFundamentalClassInDegree_injective_toSupport
    (d e : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N]
    [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin e → ℂ)) 1 N]
    (f : TopCat.of M ⟶ TopCat.of N) (hf : Function.Injective f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin e → ℂ)) ω f)
    (K : Set M) (hK : IsCompact K) (L : Set N) (hL : IsCompact L)
    (hKL : f '' K = L) (hpairs : Set.MapsTo f Kᶜ Lᶜ)
    (n : ℕ) (hd : 2 * d = n) (he : 2 * e = n) :
    HomologicalComplex.homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f hpairs) n
      (rationalCompactFundamentalClassInDegree d K hK n hd) =
    rationalCompactFundamentalClassInDegree e L hL n he := by
  subst L
  exact rationalCompactFundamentalClassInDegree_injective_localDiffeomorph d e f hf hl K hK n hd he

/-- The compact covering formula in a common homology degree, without
requiring the native model dimensions to be definitionally identical. -/
theorem rationalCompactFundamentalClassInDegree_map_degree
    (d e : ℕ) {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
    [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [IsManifold (𝓘(ℂ, Fin e → ℂ)) 1 N]
    (f : TopCat.of M ⟶ TopCat.of N) (hp : IsProperMap f)
    (hl : IsLocalDiffeomorph (𝓘(ℂ, Fin d → ℂ)) (𝓘(ℂ, Fin e → ℂ)) ω f)
    (degree : ℕ) (hdegree : ∀ y : N, Nat.card (f ⁻¹' {y}) = degree)
    (K : Set N) (hK : IsCompact K) (n : ℕ) (hd : 2 * d = n) (he : 2 * e = n) :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx)) n
      (rationalCompactFundamentalClassInDegree d (f ⁻¹' K) (hp.isCompact_preimage hK) n hd) =
    (degree : ℚ) • rationalCompactFundamentalClassInDegree e K hK n he := by
  have hde : e = d := by omega
  subst e
  subst n
  exact RationalCompactFundamental.Construction.rationalCompactFundamentalClass_map_degree d f hp hl degree hdegree K hK

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.FundamentalDegreeTransport.Construction
