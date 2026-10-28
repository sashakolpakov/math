import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductGroupIso
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.MorphismReduction

/-! # Product Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductMorphisms

noncomputable section

/-! Normalized abelian group products intertwine every group morphism.
The target may be a different family, in particular the actual dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (X Y : Over (Spec (.of (DualNumber ℂ)))) [GrpObj X] [GrpObj Y]
    [Smooth ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X).hom]
    [IsProper ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X).hom]
    [GeometricallyConnected ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X).hom]
    (e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj X))
    (d : Y ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).obj Y))
    [IsMonHom e.hom] [IsMonHom d.hom]

theorem normalizedGroupDualProduct_morphism (he : OpenProductData.NormalizesDualProductFiber ℂ e)
    (hd : OpenProductData.NormalizesDualProductFiber ℂ d) (u : X ⟶ Y) [IsMonHom u] :
    u ≫ d.hom = e.hom ≫ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).map ((Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).map u) := by
  let F := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)
  let G := Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)
  have hr : G.map (e.inv ≫ u ≫ d.hom) = G.map (F.map (G.map u)) :=
    NormalizedProduct.MorphismReduction.normalizedProductMorphism_reduction F G (Normalized.SmoothAffineDualProduct.dualProductSpecialFiberIso ℂ) X Y e d he hd u
  have hp : η[F.obj (G.obj X)] ≫ (e.inv ≫ u ≫ d.hom) =
      η[F.obj (G.obj X)] ≫ F.map (G.map u) := by
    rw [IsMonHom.one_hom (e.inv ≫ u ≫ d.hom), IsMonHom.one_hom (F.map (G.map u))]
  have h := DualPullbackMorphismRigidity.properDualPullbackMorphism_ext (G.obj X) (G.obj Y)
    (e.inv ≫ u ≫ d.hom) (F.map (G.map u)) hr hp
  apply (cancel_epi e.inv).mp
  rw [Iso.inv_hom_id_assoc]
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ProductMorphisms
