import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.RecoveryGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

/-! # Recovery Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RecoveryCompatibility

noncomputable section

/-!
# Actual bilinear equivariance gives the geometric gluing equation of the recovered product
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {X Z : Scheme.{u}} (p q : Z ⟶ X) {A B C : X.Modules}
  (hA : Line.Bundles.IsLine A) (hB : Line.Bundles.IsLine B) (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap A B C)
  (σA : (Scheme.Modules.pullback p).obj A ⟶ (Scheme.Modules.pullback q).obj A)
  (σB : (Scheme.Modules.pullback p).obj B ⟶ (Scheme.Modules.pullback q).obj B)
  (σC : (Scheme.Modules.pullback p).obj C ⟶ (Scheme.Modules.pullback q).obj C)
  (he : (BilinearPullback.pullback p hA hB β).postcomp σC = (BilinearPullback.pullback q hA hB β).precomp σA σB)

include he in
/-- Equivariance of actual pulled bilinear maps is equivariance of their represented sheaf morphisms. -/
theorem product_compatible :
    (Scheme.Modules.pullback p).map (BilinearPullback.toHom β) ≫ σC =
      Tensor.PullbackMap.pullbackMap p A B ≫ Tensor.SheafMaps.tensorMap σA σB ≫ BilinearPullback.pulledHom q hA hB β := by
  have hb := congrArg BilinearPullback.toHom he
  rw [BilinearPullback.toHom_postcomp, BilinearPullback.toHom_precomp, BilinearPullback.toHom_pullback, BilinearPullback.toHom_pullback] at hb
  calc
    _ = (Tensor.PullbackMap.pullbackMap p A B ≫ BilinearPullback.pulledHom p hA hB β) ≫ σC :=
      congrArg (fun t => t ≫ σC) (BilinearPullback.pulledHom_fac p hA hB β).symm
    _ = Tensor.PullbackMap.pullbackMap p A B ≫ (BilinearPullback.pulledHom p hA hB β ≫ σC) := Category.assoc _ _ _
    _ = _ := congrArg (fun t => Tensor.PullbackMap.pullbackMap p A B ≫ t) hb

variable {Y : Scheme.{u}} (f : X ⟶ Y) (h : p ≫ f = q ≫ f)
  (M N : Y.Modules) (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
  (a : (Scheme.Modules.pullback f).obj M ⟶ A) (b : (Scheme.Modules.pullback f).obj N ⟶ B)
  (ha : (Scheme.Modules.pullback p).map a ≫ σA =
    (Cech.MateNormalization.standardGluing f p q h).hom.app M ≫ (Scheme.Modules.pullback q).map a)
  (hb : (Scheme.Modules.pullback p).map b ≫ σB =
    (Cech.MateNormalization.standardGluing f p q h).hom.app N ≫ (Scheme.Modules.pullback q).map b)

include hA hB hM hN he ha hb in
/-- Bilinear equivariance and the two input recovery equations imply the exact product descent square. -/
theorem recovered_product_compatible :
    (Scheme.Modules.pullback p).map ((Tensor.PullbackMap.pullbackMap f M N ≫ Tensor.SheafMaps.tensorMap a b) ≫ BilinearPullback.toHom β) ≫ σC =
      (Cech.MateNormalization.standardGluing f p q h).hom.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≫
        (Scheme.Modules.pullback q).map ((Tensor.PullbackMap.pullbackMap f M N ≫ Tensor.SheafMaps.tensorMap a b) ≫ BilinearPullback.toHom β) := by
  rw [(Scheme.Modules.pullback p).map_comp _ (BilinearPullback.toHom β), (Scheme.Modules.pullback q).map_comp _ (BilinearPullback.toHom β)]
  rw [Category.assoc, product_compatible p q hA hB β σA σB σC he]
  have ht := Tensor.RecoveryGluing.tensor_compatible f p q h M N hM hN a b σA σB ha hb
  calc
    _ = ((Scheme.Modules.pullback p).map (Tensor.PullbackMap.pullbackMap f M N ≫ Tensor.SheafMaps.tensorMap a b) ≫
        Tensor.PullbackMap.pullbackMap p A B ≫ Tensor.SheafMaps.tensorMap σA σB) ≫ BilinearPullback.pulledHom q hA hB β := by simp only [Category.assoc]
    _ = ((Cech.MateNormalization.standardGluing f p q h).hom.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≫
        (Scheme.Modules.pullback q).map (Tensor.PullbackMap.pullbackMap f M N ≫ Tensor.SheafMaps.tensorMap a b) ≫ Tensor.PullbackMap.pullbackMap q A B) ≫
        BilinearPullback.pulledHom q hA hB β := congrArg (fun t => t ≫ BilinearPullback.pulledHom q hA hB β) ht
    _ = _ := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (fun t => (Cech.MateNormalization.standardGluing f p q h).hom.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) ≫
        (Scheme.Modules.pullback q).map (Tensor.PullbackMap.pullbackMap f M N ≫ Tensor.SheafMaps.tensorMap a b) ≫ t) (BilinearPullback.pulledHom_fac q hA hB β)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RecoveryCompatibility
