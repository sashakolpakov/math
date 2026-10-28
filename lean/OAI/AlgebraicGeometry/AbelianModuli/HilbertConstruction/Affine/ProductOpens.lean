import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ProductCharts
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Product Opens -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ProductOpens

noncomputable section

/-! Products of affine opens are affine over an affine base, as actual opens in the fiber product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)

theorem affine_product_open (U : X.Opens) (V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen ((pullback.fst f g ⁻¹ᵁ U) ⊓ (pullback.snd f g ⁻¹ᵁ V)) := by
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have : IsAffine (pullback (U.ι ≫ f) (V.ι ≫ g)) := inferInstance
  have h := isAffineOpen_opensRange (Open.ProductCharts.openProductChartMap f g U.ι V.ι)
  rw [Open.ProductCharts.openProductChartMap_opensRange] at h
  change IsAffineOpen ((pullback.fst f g ⁻¹ᵁ U.ι.opensRange) ⊓
    (pullback.snd f g ⁻¹ᵁ V.ι.opensRange)) at h
  rwa [U.opensRange_ι, V.opensRange_ι] at h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ProductOpens
