import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientExternalPresheafMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ExternalAffineFrameIso

/-! # Ambient Affine Pairing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientAffinePairing

noncomputable section

/-! The canonical tensor pairing into actual native Cech-factor sections is invertible on affine frame charts. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem nativeAmbientExternalSectionMap_comparison
    {X Y P : Scheme.{u}} {R : Type u} [CommRing R]
    (a : P ⟶ X) (b : P ⟶ Y) (cX : R →+* Γ(X, ⊤)) (cY : R →+* Γ(Y, ⊤))
    (hc : a.appTop.hom.comp cX = b.appTop.hom.comp cY)
    (M : X.Modules) (N : Y.Modules) (V : X.Opens) (U : Y.Opens) :
    (AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b cX cY hc M N U).app (op V) ≫
      (Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso
        (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
          ((Scheme.Modules.pullback b).obj N))) (b ⁻¹ᵁ U) (a ⁻¹ᵁ V)).hom =
    (Module.ProductForget.moduleForget R).map (ModuleCat.ofHom (AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b cX cY hc M N V U)) := by
  let e := Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso
    (UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
      ((Scheme.Modules.pullback b).obj N))) (b ⁻¹ᵁ U) (a ⁻¹ᵁ V)
  apply ConcreteCategory.hom_ext
  intro z
  let x := AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b cX cY hc M N V U z
  change e.hom (e.inv x) = x
  exact ConcreteCategory.congr_hom e.inv_hom_id x

theorem affineFrames_nativeAmbientExternalSectionMap_isIso
    {S X Y P : Scheme.{u}} [IsAffine S]
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) (M : X.Modules) (N : Y.Modules)
    (V : X.Opens) (U : Y.Opens) (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (eV : (Scheme.Modules.pullback V.ι).obj M ≅ Line.Bundles.structureModule V.toScheme)
    (eU : (Scheme.Modules.pullback U.ι).obj N ≅ Line.Bundles.structureModule U.toScheme) :
    IsIso ((AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N U).app (op V)) := by
  let β := ModuleCat.ofHom (AmbientExternalSectionPairing.ambientExternalSectionTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N V U)
  have : IsIso β := ExternalAffineFrameIso.affineFrames_ambientExternalSectionTensorMap_isIso H M N V U hV hU eV eU
  let E := (Module.ProductForget.moduleForget Γ(S, ⊤)).mapIso (asIso β)
  let F : P.carrier.Sheaf AddCommGrpCat.{u} :=
    UnderlyingAdditiveSheafExactness.ModuleSheaf.sheaf (Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback a).obj M)
      ((Scheme.Modules.pullback b).obj N))
  let α := (AmbientExternalPresheafMap.nativeAmbientExternalSectionMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N U).app (op V)
  let e := Cech.SheafFactorRestriction.IntrinsicCech.cechOpenFactorSectionsIso F (b ⁻¹ᵁ U) (a ⁻¹ᵁ V)
  have h : α ≫ e.hom = E.hom := nativeAmbientExternalSectionMap_comparison a b
    f.appTop.hom g.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N V U
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  have hE : Function.Bijective E.hom := ConcreteCategory.bijective_of_isIso E.hom
  apply (ConcreteCategory.isIso_iff_bijective α).mpr
  constructor
  · intro x y hxy
    apply hE.injective
    exact (ConcreteCategory.congr_hom h x).symm.trans
      ((congrArg e.hom hxy).trans (ConcreteCategory.congr_hom h y))
  · intro y
    obtain ⟨x, hx⟩ := hE.surjective (e.hom y)
    exact ⟨x, he.injective ((ConcreteCategory.congr_hom h x).trans hx)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AmbientAffinePairing
