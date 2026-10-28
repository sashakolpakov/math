import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine Neighborhood Inside -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineNeighborhoodInside.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual compatible affine neighborhoods of every point of a scheme section -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem section_exists_affineNeighborhoods {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y)
    (hs : s ≫ p = 𝟙 X) (x : X) :
    ∃ (U : Y.Opens) (V : X.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ V ∧
      V ≤ s ⁻¹ᵁ U ∧ U ≤ p ⁻¹ᵁ V := by
  obtain ⟨V₀, hV₀, hxV₀, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have hsx : p (s x) = x := congrArg (fun f => f x) hs
  obtain ⟨U₀, hU₀, hsxU₀, hU₀V₀⟩ := exists_isAffineOpen_mem_and_subset
    (show s x ∈ p ⁻¹ᵁ V₀ by change p (s x) ∈ V₀; rw [hsx]; exact hxV₀)
  change U₀ ≤ p ⁻¹ᵁ V₀ at hU₀V₀
  obtain ⟨V, hV, hxV, hVV₀⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V₀ ⊓ s ⁻¹ᵁ U₀ from ⟨hxV₀, hsxU₀⟩)
  change V ≤ V₀ ⊓ s ⁻¹ᵁ U₀ at hVV₀
  let q : U₀.toScheme ⟶ V₀.toScheme := Y.homOfLE hU₀V₀ ≫ morphismRestrict p V₀
  have hq : q ≫ V₀.ι = U₀.ι ≫ p := by
    dsimp only [q]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have : IsAffine U₀.toScheme := hU₀
  have : IsAffine V₀.toScheme := hV₀
  have hVV₀' : V ≤ V₀.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact fun y hy => (hVV₀ hy).1
  have hW : IsAffineOpen (q ⁻¹ᵁ (V₀.ι ⁻¹ᵁ V)) :=
    (hV.preimage_of_isOpenImmersion V₀.ι hVV₀').preimage q
  let U := U₀.ι ''ᵁ (q ⁻¹ᵁ (V₀.ι ⁻¹ᵁ V))
  have hU : IsAffineOpen U := hW.image_of_isOpenImmersion U₀.ι
  have hUeq : U = U₀ ⊓ p ⁻¹ᵁ V := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.property, ?_⟩
      have he := congrArg (fun f => f z) hq
      change V₀.ι (q z) ∈ V at hz
      change p (U₀.ι z) ∈ V
      exact he ▸ hz
    · rintro ⟨hy, hpy⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      have he := congrArg (fun f => f (⟨y, hy⟩ : U₀.toScheme)) hq
      change V₀.ι (q ⟨y, hy⟩) ∈ V
      exact he.symm ▸ hpy
  refine ⟨U, V, hU, hV, hxV, ?_, ?_⟩
  · intro y hy
    change s y ∈ U
    rw [hUeq]
    refine ⟨(hVV₀ hy).2, ?_⟩
    change p (s y) ∈ V
    exact (congrArg (fun f => f y) hs).symm ▸ hy
  · rw [hUeq]
    exact inf_le_right

end

/-! Compatible affine section neighborhoods can be chosen inside any given ambient open neighborhood. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem section_exists_affineNeighborhoods_inside {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y)
    (hs : s ≫ p = 𝟙 X) (x : X) (W : Y.Opens) (hxW : s x ∈ W) :
    ∃ (U : Y.Opens) (V : X.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ V ∧
      V ≤ s ⁻¹ᵁ U ∧ U ≤ p ⁻¹ᵁ V ∧ U ≤ W := by
  obtain ⟨V₀, hV₀, hxV₀, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have hsx : p (s x) = x := congrArg (fun f => f x) hs
  obtain ⟨U₀, hU₀, hsxU₀, hU₀W⟩ := exists_isAffineOpen_mem_and_subset
    (show s x ∈ W ⊓ p ⁻¹ᵁ V₀ from ⟨hxW, by change p (s x) ∈ V₀; rw [hsx]; exact hxV₀⟩)
  have hU₀V₀ : U₀ ≤ p ⁻¹ᵁ V₀ := fun y hy => (hU₀W hy).2
  obtain ⟨V, hV, hxV, hVV₀⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V₀ ⊓ s ⁻¹ᵁ U₀ from ⟨hxV₀, hsxU₀⟩)
  change V ≤ V₀ ⊓ s ⁻¹ᵁ U₀ at hVV₀
  let q : U₀.toScheme ⟶ V₀.toScheme := Y.homOfLE hU₀V₀ ≫ morphismRestrict p V₀
  have hq : q ≫ V₀.ι = U₀.ι ≫ p := by
    dsimp only [q]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have : IsAffine U₀.toScheme := hU₀
  have : IsAffine V₀.toScheme := hV₀
  have hVV₀' : V ≤ V₀.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact fun y hy => (hVV₀ hy).1
  have hW : IsAffineOpen (q ⁻¹ᵁ (V₀.ι ⁻¹ᵁ V)) :=
    (hV.preimage_of_isOpenImmersion V₀.ι hVV₀').preimage q
  let U := U₀.ι ''ᵁ (q ⁻¹ᵁ (V₀.ι ⁻¹ᵁ V))
  have hU : IsAffineOpen U := hW.image_of_isOpenImmersion U₀.ι
  have hUeq : U = U₀ ⊓ p ⁻¹ᵁ V := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.property, ?_⟩
      have he := congrArg (fun f => f z) hq
      change V₀.ι (q z) ∈ V at hz
      change p (U₀.ι z) ∈ V
      exact he ▸ hz
    · rintro ⟨hy, hpy⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      have he := congrArg (fun f => f (⟨y, hy⟩ : U₀.toScheme)) hq
      change V₀.ι (q ⟨y, hy⟩) ∈ V
      exact he.symm ▸ hpy
  refine ⟨U, V, hU, hV, hxV, ?_, ?_, ?_⟩
  · intro y hy
    change s y ∈ U
    rw [hUeq]
    refine ⟨(hVV₀ hy).2, ?_⟩
    change p (s y) ∈ V
    exact (congrArg (fun f => f y) hs).symm ▸ hy
  · rw [hUeq]
    exact inf_le_right

  · rw [hUeq]
    exact fun y hy => (hU₀W hy.1).1

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineNeighborhoodInside.BundleCycles
