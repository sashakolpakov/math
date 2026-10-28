import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Sum -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.Sum.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual relative affine spaces split as iterated affine spaces -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (ι κ : Type) (X : Scheme.{0})

def affineSpaceSumToIterated : AffineSpace (ι ⊕ κ) X ⟶ AffineSpace ι (AffineSpace κ X) :=
  AffineSpace.homOfVector (AffineSpace.reindex Sum.inr X)
    (fun i : ι => AffineSpace.coord X (Sum.inl i : ι ⊕ κ))

def affineSpaceIteratedToSum : AffineSpace ι (AffineSpace κ X) ⟶ AffineSpace (ι ⊕ κ) X :=
  AffineSpace.homOfVector
    ((AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) ≫ (AffineSpace κ X ↘ X))
    (Sum.elim (AffineSpace.coord (AffineSpace κ X))
      (fun k : κ => (AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X).appTop
        (AffineSpace.coord X k)))

theorem affineSpaceSumToIterated_projection :
    affineSpaceSumToIterated ι κ X ≫ (AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) =
      AffineSpace.reindex Sum.inr X := AffineSpace.homOfVector_over _ _

theorem affineSpaceIteratedToSum_projection :
    affineSpaceIteratedToSum ι κ X ≫ (AffineSpace (ι ⊕ κ) X ↘ X) =
      (AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) ≫ (AffineSpace κ X ↘ X) :=
  AffineSpace.homOfVector_over _ _

theorem affineSpaceIteratedToSum_second :
    affineSpaceIteratedToSum ι κ X ≫ AffineSpace.reindex Sum.inr X =
      (AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) := by
  apply AffineSpace.hom_ext
  · simp [affineSpaceIteratedToSum]
  · intro k
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord]
    exact AffineSpace.homOfVector_appTop_coord _ _ _

def affineSpaceSumEquiv : AffineSpace (ι ⊕ κ) X ≅ AffineSpace ι (AffineSpace κ X) where
  hom := affineSpaceSumToIterated ι κ X
  inv := affineSpaceIteratedToSum ι κ X
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · change affineSpaceSumToIterated ι κ X ≫
        (affineSpaceIteratedToSum ι κ X ≫ (AffineSpace (ι ⊕ κ) X ↘ X)) = _
      rw [affineSpaceIteratedToSum_projection, ← Category.assoc,
        affineSpaceSumToIterated_projection, AffineSpace.reindex_over, Category.id_comp]
    · intro i
      cases i with
      | inl i =>
        rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
        simp [affineSpaceSumToIterated, affineSpaceIteratedToSum]
      | inr k =>
        rw [Scheme.Hom.comp_appTop]
        change (affineSpaceSumToIterated ι κ X).appTop
          ((affineSpaceIteratedToSum ι κ X).appTop (AffineSpace.coord X (Sum.inr k))) = _
        simp only [affineSpaceIteratedToSum, AffineSpace.homOfVector_appTop_coord, Sum.elim_inr]
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          affineSpaceSumToIterated_projection, AffineSpace.reindex_appTop_coord]
        simp
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · rw [Category.assoc, affineSpaceSumToIterated_projection,
        affineSpaceIteratedToSum_second, Category.id_comp]
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      simp [affineSpaceSumToIterated, affineSpaceIteratedToSum]

theorem affineSpaceSumEquiv_over :
    (affineSpaceSumEquiv ι κ X).hom ≫
      ((AffineSpace ι (AffineSpace κ X) ↘ AffineSpace κ X) ≫ (AffineSpace κ X ↘ X)) =
        (AffineSpace (ι ⊕ κ) X ↘ X) := by
  change affineSpaceSumToIterated ι κ X ≫ _ = _
  rw [← Category.assoc, affineSpaceSumToIterated_projection, AffineSpace.reindex_over]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.Sum.BundleCycles
