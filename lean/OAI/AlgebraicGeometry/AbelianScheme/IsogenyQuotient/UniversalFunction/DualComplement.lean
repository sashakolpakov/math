import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.MapDetection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.DualScalar
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange

/-! # Dual Complement -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualComplement.Construction

noncomputable section

section

/-! Scalar duality over arbitrary bases with universal global functions follows from the
actual geometric Poincare comparison and pointed-map rigidity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

set_option backward.isDefEq.respectTransparency false in
theorem universalFunction_nativeDualMap_scalar
    {S : Scheme.{0}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (hΓ : GlobalFunctions.Construction.HasUniversalGlobalFunctions D.abelian.scheme) (n : ℕ) :
    FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap ((𝟙 A.scheme) ^ n) D D = (𝟙 D.abelian.scheme) ^ n := by
  have : IsMonHom (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap ((𝟙 A.scheme) ^ n) D D) :=
    DualMaps.Construction.universalFunction_nativeDualMap_isMonHom ((𝟙 A.scheme) ^ n) D D hΓ
  apply MapDetection.Construction.universalFunction_pointed_map_eq_of_geometric_baseChanges D.abelian.scheme D.abelian.scheme hΓ
    _ _ (IsMonHom.one_hom _) (IsMonHom.one_hom _)
  intro K _ _ s
  have hA : (Over.pullback s).map ((𝟙 A.scheme) ^ n) = (𝟙 (A.pullback s).scheme) ^ n :=
    ((Over.pullback s).homMonoidHom (X := A.scheme) (M := A.scheme)).map_pow (𝟙 A.scheme) n |>.trans
      (congrArg (fun f => f ^ n) ((Over.pullback s).map_id A.scheme))
  have hD : (Over.pullback s).map ((𝟙 D.abelian.scheme) ^ n) = (𝟙 (D.pullback s).abelian.scheme) ^ n :=
    ((Over.pullback s).homMonoidHom (X := D.abelian.scheme) (M := D.abelian.scheme)).map_pow
      (𝟙 D.abelian.scheme) n |>.trans
        (congrArg (fun f => f ^ n) ((Over.pullback s).map_id D.abelian.scheme))
  rw [FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange]
  change FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap ((Over.pullback s).map ((𝟙 A.scheme) ^ n)) (D.pullback s) (D.pullback s) = _
  exact (Noetherian.DualMaps.Construction.nativeDualMap_congr (D.pullback s) (D.pullback s) _ _ hA).trans
    ((Field.DualScalar.Construction.field_nativeDualMap_scalar (D.pullback s) n).trans hD.symm)

end

/-! Original native dual maps retain both scalar complement identities
over arbitrary bases with universal global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

theorem universalFunction_nativeDualMap_complements
    {S : Scheme.{0}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (hDA : GlobalFunctions.Construction.HasUniversalGlobalFunctions DA.abelian.scheme) (hDB : GlobalFunctions.Construction.HasUniversalGlobalFunctions DB.abelian.scheme)
    (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (v : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (n : ℕ)
    (hfv : f.hom ≫ v.hom = (𝟙 A.scheme) ^ n)
    (hvf : v.hom ≫ f.hom = (𝟙 B.scheme) ^ n) :
    FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap v.hom DB DA = (𝟙 DB.abelian.scheme) ^ n ∧
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap v.hom DB DA ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB = (𝟙 DA.abelian.scheme) ^ n := by
  constructor
  · exact (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp v.hom DB DA DB f.hom).symm.trans
      ((Noetherian.DualMaps.Construction.nativeDualMap_congr DB DB _ _ hvf).trans (universalFunction_nativeDualMap_scalar DB hDB n))
  · exact (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap_comp f.hom DA DB DA v.hom).symm.trans
      ((Noetherian.DualMaps.Construction.nativeDualMap_congr DA DA _ _ hfv).trans (universalFunction_nativeDualMap_scalar DA hDA n))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualComplement.Construction
