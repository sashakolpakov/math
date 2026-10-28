import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductOpen
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Tube

/-! # Product Rigidity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductRigidity.Construction

noncomputable section

/-!
# Completion: local rigidity for a proper integral geometric factor

If one fiber of a map from X × Y lies in an affine target open, properness
gives a base neighborhood with the same property. The proved calculation
of global functions then makes the map factor through that neighborhood.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper p]
  (q : Y ⟶ Spec (CommRingCat.of K))
  (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ p = 𝟙 _)

/-- A fiber whose image lies in an affine open has a base neighborhood on which the map
is independent of the proper factor. -/
theorem properProduct_rigidity_neighborhood (f : pullback p q ⟶ Z)
    (y : Y) (V : Z.Opens) (hV : IsAffineOpen V)
    (hy : ∀ t : (pullback p q : Scheme.{u}), pullback.snd p q t = y → f t ∈ V) :
    ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧
      ProductOpen.Construction.properProductOpenMap p q U ≫ f =
        pullback.snd p (U.ι ≫ q) ≫ U.ι ≫ AffineBaseChange.Construction.properProductSection p q e he ≫ f := by
  let B := Tube.Construction.properTubeOpen (pullback.snd p q) f V
  have hyB : y ∈ B := Tube.Construction.mem_properTubeOpen (pullback.snd p q) f V y hy
  obtain ⟨_, ⟨U₀, hU, rfl⟩, hyU, hUB⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyB B.isOpen
  let U : Y.Opens := U₀
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let g := ProductOpen.Construction.properProductOpenMap p q U ≫ f
  have hg : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply Tube.Construction.properTubeOpen_preimage_le (pullback.snd p q) f V
    change pullback.snd p q (ProductOpen.Construction.properProductOpenMap p q U t) ∈ B
    rw [← Scheme.Hom.comp_apply, ProductOpen.Construction.properProductOpenMap_snd, Scheme.Hom.comp_apply]
    exact hUB (pullback.snd p (U.ι ≫ q) t).property
  let gV : pullback p (U.ι ≫ q) ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hg
  have hgV : gV ≫ V.ι = g := IsOpenImmersion.lift_fac V.ι g hg
  have hc := congrArg (fun k => k ≫ V.ι)
    (AffineBaseChange.Construction.properIntegral_product_to_affine p (U.ι ≫ q) e he gV)
  simp only [Category.assoc, hgV] at hc
  refine ⟨U, hyU, hU, ?_⟩
  change g = _
  rw [hc]
  change pullback.snd p (U.ι ≫ q) ≫
      AffineBaseChange.Construction.properProductSection p (U.ι ≫ q) e he ≫ ProductOpen.Construction.properProductOpenMap p q U ≫ f = _
  rw [← Category.assoc (AffineBaseChange.Construction.properProductSection p (U.ι ≫ q) e he),
    ProductOpen.Construction.properProductSection_open, Category.assoc]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.ProductRigidity.Construction
