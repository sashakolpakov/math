import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineNeighborhoodInside

/-! # Morphism Neighborhoods -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.MorphismNeighborhoods

noncomputable section

/-! Every finite family of section-preserving endomorphisms admits
actual affine source and target neighborhoods over the same affine base open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affineOpen_inter_base_preimage {X Y : Scheme.{0}} (p : Y ⟶ X)
    (U : Y.Opens) (V₀ V : X.Opens) (hU : IsAffineOpen U)
    (hV₀ : IsAffineOpen V₀) (hV : IsAffineOpen V)
    (hUV₀ : U ≤ p ⁻¹ᵁ V₀) (hVV₀ : V ≤ V₀) :
    IsAffineOpen (U ⊓ p ⁻¹ᵁ V) := by
  let q : U.toScheme ⟶ V₀.toScheme := Y.homOfLE hUV₀ ≫ morphismRestrict p V₀
  have hq : q ≫ V₀.ι = U.ι ≫ p := by
    dsimp only [q]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have : IsAffine U.toScheme := hU
  have : IsAffine V₀.toScheme := hV₀
  have hVV₀' : V ≤ V₀.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact hVV₀
  have hW : IsAffineOpen (q ⁻¹ᵁ (V₀.ι ⁻¹ᵁ V)) :=
    (hV.preimage_of_isOpenImmersion V₀.ι hVV₀').preimage q
  have himage : U.ι ''ᵁ (q ⁻¹ᵁ (V₀.ι ⁻¹ᵁ V)) = U ⊓ p ⁻¹ᵁ V := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.property, ?_⟩
      have he := congrArg (fun f => f z) hq
      change V₀.ι (q z) ∈ V at hz
      change p (U.ι z) ∈ V
      exact he ▸ hz
    · rintro ⟨hy, hpy⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      have he := congrArg (fun f => f (⟨y, hy⟩ : U.toScheme)) hq
      change V₀.ι (q ⟨y, hy⟩) ∈ V
      exact he.symm ▸ hpy
  exact himage ▸ hW.image_of_isOpenImmersion U.ι

theorem section_exists_affine_morphism_neighborhoods
    {X Y : Scheme.{0}} (p : Y ⟶ X) (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)
    {ι : Type} [Finite ι] (f : ι → (Y ⟶ Y))
    (hf : ∀ i, f i ≫ p = p) (he : ∀ i, s ≫ f i = s) (x : X) :
    ∃ (U W : Y.Opens) (V : X.Opens),
      IsAffineOpen U ∧ IsAffineOpen W ∧ IsAffineOpen V ∧ x ∈ V ∧
      V ≤ s ⁻¹ᵁ W ∧ W ≤ U ∧ U ≤ p ⁻¹ᵁ V ∧
      ∀ i, W ≤ f i ⁻¹ᵁ U := by
  obtain ⟨U₀, V₀, hU₀, hV₀, hxV₀, hsU₀, hpU₀⟩ :=
    Divisors.LineBundles.Section.AffineNeighborhoodInside.BundleCycles.section_exists_affineNeighborhoods p s hs x
  have hxH : s x ∈ U₀ ⊓ ⨅ i, f i ⁻¹ᵁ U₀ := by
    refine ⟨hsU₀ hxV₀, ?_⟩
    rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro i
    change f i (s x) ∈ U₀
    have hix : f i (s x) = s x := congrArg (fun g => g x) (he i)
    exact hix.symm ▸ hsU₀ hxV₀
  obtain ⟨W₀, hW₀, hxW₀, hW₀H⟩ := exists_isAffineOpen_mem_and_subset hxH
  change W₀ ≤ U₀ ⊓ ⨅ i, f i ⁻¹ᵁ U₀ at hW₀H
  obtain ⟨V, hV, hxV, hVsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V₀ ⊓ s ⁻¹ᵁ W₀ from ⟨hxV₀, hxW₀⟩)
  change V ≤ V₀ ⊓ s ⁻¹ᵁ W₀ at hVsub
  let U := U₀ ⊓ p ⁻¹ᵁ V
  let W := W₀ ⊓ p ⁻¹ᵁ V
  have hUV : IsAffineOpen U := affineOpen_inter_base_preimage p U₀ V₀ V hU₀ hV₀ hV
    hpU₀ (le_trans hVsub inf_le_left)
  have hWV : IsAffineOpen W := affineOpen_inter_base_preimage p W₀ V₀ V hW₀ hV₀ hV
    (le_trans (le_trans hW₀H inf_le_left) hpU₀) (le_trans hVsub inf_le_left)
  refine ⟨U, W, V, hUV, hWV, hV, hxV, ?_, ?_, inf_le_right, ?_⟩
  · intro y hy
    refine ⟨(hVsub hy).2, ?_⟩
    change p (s y) ∈ V
    exact (congrArg (fun g => g y) hs).symm ▸ hy
  · exact inf_le_inf (le_trans hW₀H inf_le_left) le_rfl
  · intro i y hy
    refine ⟨?_, ?_⟩
    · have h := (hW₀H hy.1).2
      rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] at h
      exact h i
    · change p (f i y) ∈ V
      exact (congrArg (fun g => g y) (hf i)).symm ▸ hy.2

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.MorphismNeighborhoods
