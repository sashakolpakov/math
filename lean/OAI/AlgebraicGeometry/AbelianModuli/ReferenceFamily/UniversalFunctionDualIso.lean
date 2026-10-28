import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualPoincare

/-! # Universal Function Dual Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFunctionDualIso

noncomputable section

/-! The actual represented dual of a group-scheme isomorphism over
an arbitrary base, including its normalized Poincare comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g h : ℕ}
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]

def originalNativeDualIso : DB.abelian.scheme ≅ DA.abelian.scheme where
  hom := AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DA DB
  inv := AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.inv DB DA
  hom_inv_id := by
    rw [← AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp]
    exact (AbelianScheme.IsogenyQuotient.Noetherian.DualMaps.Construction.nativeDualMap_congr DB DB _ _ e.inv_hom_id).trans (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_id DB)
  inv_hom_id := by
    rw [← AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp]
    exact (AbelianScheme.IsogenyQuotient.Noetherian.DualMaps.Construction.nativeDualMap_congr DA DA _ _ e.hom_inv_id).trans (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_id DA)

theorem originalNativeDualIso_hom_isMonHom
    (hDB : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions DB.abelian.scheme) :
    IsMonHom (originalNativeDualIso DA DB e).hom :=
  AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps.Construction.universalFunction_nativeDualMap_isMonHom e.hom DA DB hDB

theorem originalNativeDualIso_inv_isMonHom
    (hDA : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions DA.abelian.scheme) :
    IsMonHom (originalNativeDualIso DA DB e).inv :=
  AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps.Construction.universalFunction_nativeDualMap_isMonHom e.inv DB DA hDA

theorem originalNativeDualIso_poincare (hB : AbelianScheme.IsogenyQuotient.GlobalFunctions.Construction.HasUniversalGlobalFunctions B.scheme) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((originalNativeDualIso DA DB e).inv ⊗ₘ e.hom).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare := by
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.inv DB DA ⊗ₘ e.hom).left
    (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare
  have h := congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DA.abelian.scheme ⊗ₘ e.hom).left)
    (AbelianScheme.IsogenyQuotient.UniversalFunction.DualPoincare.Construction.universalFunction_nativeDualMap_poincare DB DA hB e.inv)
  simp only [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, e.hom_inv_id] at h
  simpa only [tensorHom_id, id_whiskerRight, Over.id_left, HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFunctionDualIso
