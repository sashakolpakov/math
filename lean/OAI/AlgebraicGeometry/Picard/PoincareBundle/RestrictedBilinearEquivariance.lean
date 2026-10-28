import OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedTensorSymmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.EquivariantLineContraction

/-! # Restricted Bilinear Equivariance -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedBilinearEquivariance

noncomputable section

/-! Equivariance of an actual tensor formula restricts to the genuine pulled-back bilinear formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LinePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedLineEquivariance

theorem change_source {C : Type*} [Category C] (F : C ⥤ C) {A B D : C}
    (r : A ≅ B) (e : A ≅ D) (a : F.obj A ≅ A) (b : F.obj B ≅ B) (d : F.obj D ≅ D)
    (hr : F.mapIso r ≪≫ b = a ≪≫ r) (he : F.mapIso e ≪≫ d = a ≪≫ e) :
    F.mapIso (r.symm ≪≫ e) ≪≫ d = b ≪≫ (r.symm ≪≫ e) := by
  have h := Line.SymmetryFibers.inverse_square (F.mapIso r) r a b hr
  rw [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc, he,
    ← Iso.trans_assoc, h, Iso.trans_assoc]

theorem toHom_equation {X : Scheme.{u}} (g : X ⟶ X) {M N P : X.Modules}
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (a : (Scheme.Modules.pullback g).obj M ≅ M) (b : (Scheme.Modules.pullback g).obj N ≅ N)
    (c : (Scheme.Modules.pullback g).obj P ≅ P) (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N ≅ P)
    (he : (Scheme.Modules.pullback g).mapIso e ≪≫ c =
      (Tensor.LinePullback.pullbackIso g M N hM hN ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b) ≪≫ e) :
    (Scheme.Modules.pullback g).map (Bilinear.BilinearPullback.toHom (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P e.hom)) ≫ c.hom =
      (Tensor.LinePullback.pullbackIso g M N hM hN).hom ≫ (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a b).hom ≫
        Bilinear.BilinearPullback.toHom (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N P e.hom) := by
  simpa only [Bilinear.BilinearPullback.toHom, Equiv.symm_apply_apply, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc] using congrArg Iso.hom he

variable {S : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y) (g : Y ⟶ Y) (b : X ⟶ X)
  (h : b ≫ p = p ≫ g) (M N P : Line.Bundles.LineBundle Y.left)
  (a : (Scheme.Modules.pullback g.left).obj M.sheaf ≅ M.sheaf)
  (d : (Scheme.Modules.pullback g.left).obj N.sheaf ≅ N.sheaf)
  (c : (Scheme.Modules.pullback g.left).obj P.sheaf ≅ P.sheaf)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M.sheaf N.sheaf ≅ P.sheaf)

/-- The restricted tensor formula uses the canonical tensor pullback comparison. -/
def formula : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback p.left).obj M.sheaf)
    ((Scheme.Modules.pullback p.left).obj N.sheaf) ≅ (Scheme.Modules.pullback p.left).obj P.sheaf :=
  (Tensor.LinePullback.pullbackIso p.left M.sheaf N.sheaf M.isLine N.isLine).symm ≪≫
    (Scheme.Modules.pullback p.left).mapIso e

theorem formula_equivariant
    (he : (Scheme.Modules.pullback g.left).mapIso e ≪≫ c =
      (Tensor.LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a d) ≪≫ e) :
    (Scheme.Modules.pullback b.left).mapIso (formula p M N P e) ≪≫ RestrictedLineEquivariance.symmetry p g b h P c =
      (Tensor.LinePullback.pullbackIso b.left ((Scheme.Modules.pullback p.left).obj M.sheaf) ((Scheme.Modules.pullback p.left).obj N.sheaf)
        (M.isLine.pullback p.left) (N.isLine.pullback p.left) ≪≫
        AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (RestrictedLineEquivariance.symmetry p g b h M a) (RestrictedLineEquivariance.symmetry p g b h N d)) ≪≫ formula p M N P e := by
  let z := Tensor.LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a d
  have ht := RestrictedTensorSymmetry.tensor_symmetry p g b h M N a d
  have hf := RestrictedLineEquivariance.equivariant p g b h (Tensor.LineBundles.tensor M N) z P e c he
  exact change_source (Scheme.Modules.pullback b.left)
    (Tensor.LinePullback.pullbackIso p.left M.sheaf N.sheaf M.isLine N.isLine)
    ((Scheme.Modules.pullback p.left).mapIso e)
    (RestrictedLineEquivariance.symmetry p g b h (Tensor.LineBundles.tensor M N) z)
    (Tensor.LinePullback.pullbackIso b.left ((Scheme.Modules.pullback p.left).obj M.sheaf) ((Scheme.Modules.pullback p.left).obj N.sheaf)
      (M.isLine.pullback p.left) (N.isLine.pullback p.left) ≪≫
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (RestrictedLineEquivariance.symmetry p g b h M a) (RestrictedLineEquivariance.symmetry p g b h N d))
    (RestrictedLineEquivariance.symmetry p g b h P c) ht hf

/-- Contracting an invariant restricted section preserves the actual descended formula symmetry. -/
theorem contraction_equivariant
    (he : (Scheme.Modules.pullback g.left).mapIso e ≪≫ c =
      (Tensor.LinePullback.pullbackIso g.left M.sheaf N.sheaf M.isLine N.isLine ≪≫ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr a d) ≪≫ e)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left ⟶ (Scheme.Modules.pullback p.left).obj M.sheaf)
    (hs : Bilinear.ContractionPullback.pulledSection b.left s ≫ (RestrictedLineEquivariance.symmetry p g b h M a).hom = s) :
    (Scheme.Modules.pullback b.left).map
        (Bilinear.Contraction.contractLeft (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (formula p M N P e).hom) s) ≫
        (RestrictedLineEquivariance.symmetry p g b h P c).hom =
      (RestrictedLineEquivariance.symmetry p g b h N d).hom ≫
        Bilinear.Contraction.contractLeft (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (formula p M N P e).hom) s := by
  apply EquivariantLineContraction.contraction_equivariant b.left
    (M.isLine.pullback p.left) (N.isLine.pullback p.left)
    (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _ (formula p M N P e).hom)
    (RestrictedLineEquivariance.symmetry p g b h M a) (RestrictedLineEquivariance.symmetry p g b h N d) (RestrictedLineEquivariance.symmetry p g b h P c) _ s hs
  exact toHom_equation b.left (M.isLine.pullback p.left) (N.isLine.pullback p.left)
    (RestrictedLineEquivariance.symmetry p g b h M a) (RestrictedLineEquivariance.symmetry p g b h N d) (RestrictedLineEquivariance.symmetry p g b h P c) (formula p M N P e)
    (formula_equivariant p g b h M N P a d c e he)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RestrictedBilinearEquivariance
