import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Space

/-! # Zero Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroNaturality.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual affine-line zero section is natural under every base morphism -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineLineZeroSection_naturality {X Y : Scheme.{0}} (g : X ⟶ Y) :
    Space.BundleCycles.affineLineZeroSection X ≫ AffineSpace.map PUnit g = g ≫ Space.BundleCycles.affineLineZeroSection Y := by
  change AffineSpace.homOfVector (𝟙 X) (fun _ : PUnit => 0) ≫ AffineSpace.map PUnit g =
    g ≫ AffineSpace.homOfVector (𝟙 Y) (fun _ : PUnit => 0)
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, AffineSpace.map_over, AffineSpace.homOfVector_over,
      AffineSpace.homOfVector_over_assoc, Category.id_comp, Category.comp_id]
  · intro i
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
      AffineSpace.homOfVector_appTop_coord, map_zero]

theorem affineLineZeroSection_isPullback {X Y : Scheme.{0}} (g : X ⟶ Y) :
    IsPullback g (Space.BundleCycles.affineLineZeroSection X) (Space.BundleCycles.affineLineZeroSection Y) (AffineSpace.map PUnit g) := by
  have h : IsPullback g (Space.BundleCycles.affineLineZeroSection X ≫ Charts.BundleCycles.affineLineProjection X)
      (Space.BundleCycles.affineLineZeroSection Y ≫ Charts.BundleCycles.affineLineProjection Y) g := by
    rw [Space.BundleCycles.affineLineZeroSection_projection, Space.BundleCycles.affineLineZeroSection_projection]
    exact IsPullback.of_vert_isIso ⟨by simp only [Category.comp_id, Category.id_comp]⟩
  exact h.of_bot (affineLineZeroSection_naturality g).symm (AffineSpace.isPullback_map (n := PUnit) g)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ZeroNaturality.BundleCycles
