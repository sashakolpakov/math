import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

/-! # Pullback Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackNaturality

noncomputable section

/-!
# Naturality of pulled-back bilinear line-bundle maps in both input factors
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

/-- An isomorphic comparison square gives the corresponding square for its inverse comparisons. -/
theorem inverse_square {C : Type*} [Category C] {A B U V : C}
    (c : A ≅ U) (d : B ≅ V) (a : A ⟶ B) (b : U ⟶ V)
    (h : a ≫ d.hom = c.hom ≫ b) : c.inv ≫ a = b ≫ d.inv := by
  apply (cancel_mono d.hom).mp
  rw [Category.assoc, h, Iso.inv_hom_id_assoc, Category.assoc, d.inv_hom_id, Category.comp_id]

end

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' N N' P : Y.Modules}
  (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
  (hM' : Line.Bundles.IsLine M') (hN' : Line.Bundles.IsLine N')
  (a : M' ⟶ M) (b : N' ⟶ N)

/-- The inverse actual tensor pullback comparison is natural in both line-bundle inputs. -/
theorem inverse_comparison_naturality :
    (Tensor.LinePullback.pullbackIso f M' N' hM' hN').inv ≫ (Scheme.Modules.pullback f).map (Tensor.SheafMaps.tensorMap a b) =
      Tensor.SheafMaps.tensorMap ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) ≫
        (Tensor.LinePullback.pullbackIso f M N hM hN).inv :=
  inverse_square (Tensor.LinePullback.pullbackIso f M' N' hM' hN')
    (Tensor.LinePullback.pullbackIso f M N hM hN) _ _
    (Tensor.PullbackMap.pullbackMap_naturality f a b)

/-- Arbitrary geometric pullback respects precomposition of the two bilinear input maps. -/
theorem pullback_precomp (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) :
    BilinearPullback.pullback f hM' hN' (β.precomp a b) =
      (BilinearPullback.pullback f hM hN β).precomp ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
  change BilinearPullback.toHom _ = BilinearPullback.toHom _
  rw [BilinearPullback.toHom_pullback, BilinearPullback.toHom_precomp, BilinearPullback.toHom_pullback]
  unfold BilinearPullback.pulledHom
  rw [BilinearPullback.toHom_precomp, Functor.map_comp, ← Category.assoc, inverse_comparison_naturality f hM hN hM' hN' a b,
    Category.assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackNaturality
