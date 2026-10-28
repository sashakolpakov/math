import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteCompactRestriction
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteComparisonNaturality

/-! # Locally Finite Restriction Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteRestrictionNaturality.Cycles

noncomputable section

/-!
# Proper pushforward commutes with compact relative restriction

A proper map carries agreement near the inverse image of a compact set to
agreement near that compact set. Applying this to the genuine finite compact
truncation identifies the two actual chain maps to relative singular chains.
The induced homology square follows by functoriality. Neither ambient space
is assumed compact.
-/

open Set Function _root_.CategoryTheory
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{0}}

/-- Proper coefficient pushforward preserves agreement near a subset when
the original coefficients agree near its inverse image. -/
theorem locallyFiniteProperMap_agrees_of_agrees_near {R : Type*} [Semiring R]
    (f : X ⟶ Y) (hf : IsProperMap f) (K : Set Y) (n : ℕ)
    (c d : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains R X n)
    (hcd : ∀ σ, (LocallyFiniteChains.Cycles.singularSimplexImage X n σ ∩ f ⁻¹' K).Nonempty → c σ = d σ)
    (τ : (TopCat.toSSet.obj Y).obj (.op ⦋n⦌))
    (hτ : (LocallyFiniteChains.Cycles.singularSimplexImage Y n τ ∩ K).Nonempty) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperMap R f hf n c τ = LocallyFiniteProperMap.Cycles.locallyFiniteProperMap R f hf n d τ := by
  simp only [LocallyFiniteProperMap.Cycles.locallyFiniteProperMap_apply]
  apply finsum_mem_congr rfl
  intro σ hσ
  apply hcd σ
  obtain ⟨y, hy, hyK⟩ := hτ
  have hyimage : y ∈ f '' LocallyFiniteChains.Cycles.singularSimplexImage X n σ := by
    rw [← LocallyFiniteProperMap.Cycles.singularSimplexImage_postcompose f n σ, hσ]
    exact hy
  obtain ⟨x, hx, hxy⟩ := hyimage
  exact ⟨x, hx, by simpa only [Set.mem_preimage, hxy] using hyK⟩

/-- Coefficients of the ordinary pushforward are the coefficients of the
actual proper locally finite pushforward of the same finite chain. -/
theorem ordinarySingularPushforward_coefficients (f : X ⟶ Y) (hf : IsProperMap f)
    (n : ℕ) (a : (LocalHomology.Cycles.integralSingularChains X).X n)
    (τ : (TopCat.toSSet.obj Y).obj (.op ⦋n⦌)) :
    LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ Y n ((LocalHomology.Cycles.integralSingularChainFunctor.map f).f n a) τ =
      LocallyFiniteProperMap.Cycles.locallyFiniteProperMap ℤ f hf n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℤ X n a) τ := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (LocallyFiniteComparisonNaturality.Cycles.ordinaryToLocallyFiniteChainMap_naturality ℤ f hf) n) a
  change LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℤ Y n ((LocalHomology.Cycles.integralSingularChainFunctor.map f).f n a) =
    LocallyFiniteProperMap.Cycles.locallyFiniteProperMap ℤ f hf n (LocallyFiniteCompact.Cycles.ordinaryToLocallyFinite ℤ X n a) at h
  exact congrArg (fun z : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ Y n => z τ) h

/-- Pushing forward the finite source truncation near the compact inverse
image agrees near K with pushing forward the entire locally finite chain. -/
theorem locallyFiniteProperMap_truncation_agrees (f : X ⟶ Y) (hf : IsProperMap f)
    (K : Set Y) (hK : IsCompact K) (n : ℕ) (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n)
    (τ : (TopCat.toSSet.obj Y).obj (.op ⦋n⦌))
    (hτ : (LocallyFiniteChains.Cycles.singularSimplexImage Y n τ ∩ K).Nonempty) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperMap ℤ f hf n c τ =
      LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ Y n
        ((LocalHomology.Cycles.integralSingularChainFunctor.map f).f n
          (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X (f ⁻¹' K) (hf.isCompact_preimage hK) n c)) τ := by
  rw [ordinarySingularPushforward_coefficients f hf]
  apply locallyFiniteProperMap_agrees_of_agrees_near f hf K n c _ ?_ τ hτ
  intro σ hσ
  change c σ = LocallyFiniteCompact.Cycles.ordinarySingularChainCoefficients ℤ X n
    (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X (f ⁻¹' K) (hf.isCompact_preimage hK) n c) σ
  rw [LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation_coefficients, ite_eq_left hσ]

/-- Degreewise compact restriction commutes with actual proper pushforward
and the ordinary map of relative singular chains. -/
theorem locallyFiniteCompactRestrictionDegree_naturality (f : X ⟶ Y)
    (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) (n : ℕ)
    (c : LocallyFiniteChains.Cycles.LocallyFiniteSingularChains ℤ X n) :
    LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestrictionDegree Y K hK n (LocallyFiniteProperMap.Cycles.locallyFiniteProperMap ℤ f hf n c) =
      (LocalHomology.Cycles.relativeSingularChainsMap f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ)
        (fun _ hx => hx)).f n
        (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestrictionDegree X (f ⁻¹' K)
          (hf.isCompact_preimage hK) n c) := by
  let a := LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactTruncation X (f ⁻¹' K) (hf.isCompact_preimage hK) n c
  calc
    _ = (LocalHomology.Cycles.relativeChainProjection Y Kᶜ).f n
        ((LocalHomology.Cycles.integralSingularChainFunctor.map f).f n a) := by
      apply LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestrictionDegree_eq_of_agrees
      intro τ hτ
      exact locallyFiniteProperMap_truncation_agrees f hf K hK n c τ hτ
    _ = _ := by
      have h := ConcreteCategory.congr_hom
        (HomologicalComplex.congr_hom
          (LocalHomology.Cycles.relativeChainProjection_naturality f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ)
            (fun _ hx => hx)) n) a
      exact h.symm

/-- The genuine chain-level naturality square for compact relative
restriction. Compactness of the inverse image follows from properness. -/
@[reassoc]
theorem locallyFiniteCompactRestriction_naturality (f : X ⟶ Y)
    (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperChainMap ℤ f hf ≫ LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction Y K hK =
      LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactRestriction X (f ⁻¹' K) (hf.isCompact_preimage hK) ≫
        LocalHomology.Cycles.relativeSingularChainsMap f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact locallyFiniteCompactRestrictionDegree_naturality f hf K hK n c

/-- Proper pushforward has the corresponding naturality square on genuine
locally finite and relative integral singular homology. -/
@[reassoc]
theorem locallyFiniteCompactHomologyRestriction_naturality (f : X ⟶ Y)
    (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) (n : ℕ) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ f hf n ≫
        LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction Y K hK n =
      LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X (f ⁻¹' K) (hf.isCompact_preimage hK) n ≫
        LocalHomology.Cycles.relativeSingularHomologyMap f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx) n := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun g => HomologicalComplex.homologyMap g n)
      (locallyFiniteCompactRestriction_naturality f hf K hK)

/-- Elementwise compact-restriction compatibility, for applying the square
to an actual locally finite homology class. -/
theorem locallyFiniteCompactHomologyRestriction_naturality_apply (f : X ⟶ Y)
    (hf : IsProperMap f) (K : Set Y) (hK : IsCompact K) (n : ℕ)
    (c : (LocallyFiniteComplex.Cycles.locallyFiniteSingularComplex ℤ X).homology n) :
    LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction Y K hK n
        (LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ f hf n c) =
      LocalHomology.Cycles.relativeSingularHomologyMap f (A := (f ⁻¹' K)ᶜ) (B := Kᶜ) (fun _ hx => hx) n
        (LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X (f ⁻¹' K)
          (hf.isCompact_preimage hK) n c) :=
  ConcreteCategory.congr_hom (locallyFiniteCompactHomologyRestriction_naturality f hf K hK n) c

/-- The local restriction of a proper pushforward at a point comes from
restriction to the whole compact fiber over that point. -/
@[reassoc]
theorem locallyFinitePointHomologyRestriction_naturality (f : X ⟶ Y)
    (hf : IsProperMap f) (y : Y) (n : ℕ) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ f hf n ≫ LocallyFiniteCompactRestriction.Cycles.locallyFinitePointHomologyRestriction Y y n =
      LocallyFiniteCompactRestriction.Cycles.locallyFiniteCompactHomologyRestriction X (f ⁻¹' {y})
          (hf.isCompact_preimage isCompact_singleton) n ≫
        LocalHomology.Cycles.relativeSingularHomologyMap f (A := (f ⁻¹' {y})ᶜ) (B := {y}ᶜ)
          (fun _ hx => hx) n :=
  locallyFiniteCompactHomologyRestriction_naturality f hf {y} isCompact_singleton n

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteRestrictionNaturality.Cycles
