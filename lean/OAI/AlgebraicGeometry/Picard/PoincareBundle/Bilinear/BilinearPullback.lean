import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback

/-! # Bilinear Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

noncomputable section

/-!
# Pullback of actual bilinear structure maps on line bundles
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps

/-- The actual sheaf morphism represented by a bilinear structure map. -/
def toHom {X : Scheme.{u}} {M N P : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ⟶ P :=
  (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).symm β

/-- Postcomposition of bilinear maps is postcomposition of their represented sheaf morphisms. -/
theorem toHom_postcomp {X : Scheme.{u}} {M N P Q : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (t : P ⟶ Q) : toHom (β.postcomp t) = toHom β ≫ t := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N Q).injective
  rw [AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv_postcomp]
  exact (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N Q).apply_symm_apply _ |>.trans
    (congrArg (fun b => b.postcomp t) ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).apply_symm_apply β)).symm

/-- Precomposition of bilinear maps is the canonical tensor map of their represented morphisms. -/
theorem toHom_precomp {X : Scheme.{u}} {M M' N N' P : X.Modules} (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)
    (a : M' ⟶ M) (b : N' ⟶ N) : toHom (β.precomp a b) = Tensor.SheafMaps.tensorMap a b ≫ toHom β := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M' N' P).injective
  rw [Tensor.SheafMaps.tensorMap_precomp]
  exact (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M' N' P).apply_symm_apply _ |>.trans
    (congrArg (fun z => z.precomp a b) ((AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P).apply_symm_apply β)).symm

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M N P : Y.Modules}
  (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N) (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P)

/-- Pullback of the represented bilinear morphism uses the inverse canonical tensor comparison. -/
def pulledHom :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) ⟶
      (Scheme.Modules.pullback f).obj P :=
  (Tensor.LinePullback.pullbackIso f M N hM hN).inv ≫ (Scheme.Modules.pullback f).map (toHom β)

/-- The actual bilinear structure map after arbitrary scheme pullback. -/
def pullback :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)
      ((Scheme.Modules.pullback f).obj P) :=
  AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (pulledHom f hM hN β)

/-- Pulling back the bilinear structure retains exactly its represented sheaf map. -/
theorem toHom_pullback : toHom (BilinearPullback.pullback f hM hN β) = pulledHom f hM hN β :=
  (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm_apply_apply _

/-- The pulled-back structure map is the original sheaf pullback through the canonical tensor isomorphism. -/
theorem pulledHom_fac :
    (Tensor.LinePullback.pullbackIso f M N hM hN).hom ≫ pulledHom f hM hN β =
      (Scheme.Modules.pullback f).map (toHom β) := by
  unfold pulledHom
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Pullback of bilinear structure maps respects postcomposition on their target sheaves. -/
theorem pullback_postcomp {Q : Y.Modules} (t : P ⟶ Q) :
    BilinearPullback.pullback f hM hN (β.postcomp t) = (BilinearPullback.pullback f hM hN β).postcomp ((Scheme.Modules.pullback f).map t) := by
  apply (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm.injective
  change toHom _ = toHom _
  rw [toHom_pullback, toHom_postcomp, toHom_pullback]
  unfold pulledHom
  rw [toHom_postcomp, Functor.map_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback
