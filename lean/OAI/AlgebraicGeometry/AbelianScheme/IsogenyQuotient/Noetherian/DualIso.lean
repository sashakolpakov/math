import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualMaps
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualPoincare

/-! # Dual Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualIso.Construction

noncomputable section

/-! Native Picard pullback gives the full dual isomorphism, including
the actual normalized Poincare class, over a Noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} [IsLocallyNoetherian S] {g h : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]

def noetherianNativeDualIso : DB.abelian.scheme ≅ DA.abelian.scheme where
  hom := FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DA DB
  inv := FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.inv DB DA
  hom_inv_id := by
    rw [← FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp]
    exact (DualMaps.Construction.nativeDualMap_congr DB DB _ _ e.inv_hom_id).trans (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_id DB)
  inv_hom_id := by
    rw [← FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp]
    exact (DualMaps.Construction.nativeDualMap_congr DA DA _ _ e.hom_inv_id).trans (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_id DA)

instance noetherianNativeDualIso_hom_isMonHom :
    IsMonHom (noetherianNativeDualIso DA DB e).hom :=
  DualMaps.Construction.noetherian_nativeDualMap_isMonHom e.hom DA DB

instance noetherianNativeDualIso_inv_isMonHom :
    IsMonHom (noetherianNativeDualIso DA DB e).inv :=
  DualMaps.Construction.noetherian_nativeDualMap_isMonHom e.inv DB DA

theorem noetherianNativeDualIso_poincare :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((noetherianNativeDualIso DA DB e).inv ⊗ₘ e.hom).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.inv DB DA ⊗ₘ e.hom).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare
  have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DA.abelian.scheme ⊗ₘ e.hom).left)
    (DualPoincare.Construction.noetherian_nativeDualMap_poincare DB DA e.inv)
  simp only [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, e.hom_inv_id] at h
  simpa only [tensorHom_id, id_whiskerRight, Over.id_left, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.DualIso.Construction
