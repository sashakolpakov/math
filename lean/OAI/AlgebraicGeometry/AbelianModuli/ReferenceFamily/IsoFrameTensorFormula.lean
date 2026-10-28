import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineBundleIsoFrames
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorId
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleRightTensorMap

/-! # Iso Frame Tensor Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsoFrameTensorFormula

noncomputable section

/-! The isomorphism-to-frame equivalence uses the actual binary tensor
map. These formulas expose its section-level operation for base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u
variable {X : Scheme.{u}}

local instance isoFrameTensorFormula_monoidal : MonoidalCategory X.Modules :=
  SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance isoFrameTensorFormula_presheafMonoidal : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

theorem isoFrame_tensorMap_eq {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f g = Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.map f g := by
  apply (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _).injective
  rw [← HilbertConstruction.Tensor.Bifunctor.tensorBilinear_postcomp, HilbertConstruction.Tensor.Bifunctor.tensorModuleMap_spec]
  have he := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_left
    (f.val ⊗ₘ g.val) (𝟙 (HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N'))
  change HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv M N (HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N')
      (Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.map f g ≫ 𝟙 _) =
    (f.val ⊗ₘ g.val) ≫ HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv M' N' (HilbertConstruction.Tensor.ProductSheaf.tensorModule M' N') (𝟙 _) at he
  rw [Category.comp_id] at he
  change (HilbertConstruction.Tensor.Bifunctor.tensorBilinear M' N').precomp f g =
    HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ofTensorPresheafHom
      (HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv M N _ (Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.map f g))
  rw [he]
  ext U x y
  change _ = ((HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv M' N' _ (𝟙 _)).app (.op U))
    ((f.val ⊗ₘ g.val).app (.op U) (x ⊗ₜ y))
  erw [PresheafOfModulesOfCommRing.Monoidal.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul]
  rfl

theorem lineBundleIsoFrameEquivOfPairing_apply (L K D : HilbertConstruction.Line.Bundles.LineBundle X)
    (e : (L.tensor D).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule X) (u : L.sheaf ≅ K.sheaf) :
    LineBundleIsoFrames.lineBundleIsoFrameEquivOfPairing L K D e u =
      e.symm ≪≫ HilbertConstruction.Tensor.Bifunctor.tensorModuleMapIso u (Iso.refl D.sheaf) := by
  apply Iso.ext
  change (e.inv ≫ (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso L.sheaf D.sheaf).inv) ≫
      (SheafCohomology.Projective.InvertibleTensorEquivalence.invertibleRightTensorEquivalence D.sheaf (Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.invertible D)).functor.map u.hom ≫
        (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso K.sheaf D.sheaf).hom = e.inv ≫ HilbertConstruction.Tensor.Bifunctor.tensorModuleMap u.hom (𝟙 D.sheaf)
  rw [SheafCohomology.Projective.InvertibleRightTensorMap.invertibleRightTensorEquivalence_map, ← tensorHom_id]
  have h := congrArg (fun a => a ≫ (SheafCohomology.Projective.TensorSections.monoidalTensorObjIso K.sheaf D.sheaf).hom)
    (SheafCohomology.Projective.TensorFrameSections.monoidalTensorObjIso_inv_natural u.hom (𝟙 D.sheaf))
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc] at h
  erw [Category.assoc]
  exact congrArg (e.inv ≫ ·) (h.symm.trans (isoFrame_tensorMap_eq u.hom (𝟙 D.sheaf)).symm)

theorem lineIsoPairingExpansion {C : Type*} [Category C] {A B C' D E F : C}
    (a : A ≅ B) (b : A ≅ C') (c : C' ≅ D) (d : B ≅ E) (e : E ≅ F) :
    Iso.refl D ≪≫ ((a.symm ≪≫ b ≪≫ c).symm ≪≫ d) ≪≫ e =
      c.symm ≪≫ b.symm ≪≫ a ≪≫ d ≪≫ e := by
  ext
  simp

theorem pulledLineBundleIsoFrameEquiv_apply {Y : Scheme.{u}} (f : Y ⟶ X)
    (L K : HilbertConstruction.Line.Bundles.LineBundle X) (u : (L.pullback f).sheaf ≅ (K.pullback f).sheaf) :
    LineBundleIsoFrames.pulledLineBundleIsoFrameEquiv f L K u =
      (HilbertConstruction.Line.Bundles.structureModulePullbackIso f).symm ≪≫
        (Scheme.Modules.pullback f).mapIso (Quotients.FiniteDescent.DualEvaluationIs.Construction.DualEvaluation.iso L).symm ≪≫
          HilbertConstruction.Line.Bundles.LineBundle.tensorBaseChangeIso f L (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L) ≪≫
            HilbertConstruction.Tensor.Bifunctor.tensorModuleMapIso u (Iso.refl ((Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L).pullback f).sheaf) ≪≫
              (HilbertConstruction.Line.Bundles.LineBundle.tensorBaseChangeIso f K (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L)).symm := by
  let D := Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L
  let e : ((L.pullback f).tensor (D.pullback f)).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule Y :=
    (HilbertConstruction.Line.Bundles.LineBundle.tensorBaseChangeIso f L D).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (Quotients.FiniteDescent.DualEvaluationIs.Construction.DualEvaluation.iso L) ≪≫ HilbertConstruction.Line.Bundles.structureModulePullbackIso f
  change (Iso.refl (HilbertConstruction.Line.Bundles.structureModule Y)).symm ≪≫
    LineBundleIsoFrames.lineBundleIsoFrameEquivOfPairing (L.pullback f) (K.pullback f) (D.pullback f) e u ≪≫
      (HilbertConstruction.Line.Bundles.LineBundle.tensorBaseChangeIso f K D).symm = _
  rw [lineBundleIsoFrameEquivOfPairing_apply]
  exact lineIsoPairingExpansion (HilbertConstruction.Line.Bundles.LineBundle.tensorBaseChangeIso f L D)
    ((Scheme.Modules.pullback f).mapIso (Quotients.FiniteDescent.DualEvaluationIs.Construction.DualEvaluation.iso L)) (HilbertConstruction.Line.Bundles.structureModulePullbackIso f)
    (HilbertConstruction.Tensor.Bifunctor.tensorModuleMapIso u (Iso.refl (D.pullback f).sheaf)) (HilbertConstruction.Line.Bundles.LineBundle.tensorBaseChangeIso f K D).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IsoFrameTensorFormula
