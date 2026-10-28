import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange

/-! # Frame Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.FrameCoordinates

noncomputable section

section

/-! The actual tensor-restriction isomorphism carries the original
bilinear section map to the canonical bilinear map on the restricted
factors. This fixes the meaning of tensor frames on common opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section Yoneda

variable {C : Type*} [Category C] {F : C ⥤ Type*} {X Y : C}

theorem corepresentable_iso_unit (R : F.CorepresentableBy X) (T : F.CorepresentableBy Y) :
    R.homEquiv (R.uniqueUpToIso T).hom = T.homEquiv (𝟙 Y) := by
  exact R.homEquiv.apply_symm_apply _

end Yoneda

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)

theorem restrictedTensor_identity_meaning :
    (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictedCorepresentable f M N).homEquiv (𝟙 _) =
      (SheafTensorMaps.tensorBilinear M N).restrict f := by
  apply (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N ((HilbertConstruction.Tensor.ProductSheaf.tensorModule M N).restrict f)).injective
  change (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N _)
    ((HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictHomEquiv f M N _).symm
      (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N _
        ((Scheme.Modules.restrictAdjunction f).homEquiv _ _ (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_id]
  exact (SheafTensorMaps.tensorBilinear_postcomp _).symm.trans ((SheafTensorMaps.tensorBilinear M N).restrict_unit_naturality f).symm

theorem tensorModuleRestrictIso_bilinear :
    ((SheafTensorMaps.tensorBilinear M N).restrict f).postcomp (HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso f M N).hom =
      SheafTensorMaps.tensorBilinear (M.restrict f) (N.restrict f) := by
  have h := corepresentable_iso_unit (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictedCorepresentable f M N)
    (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.corepresentable (M.restrict f) (N.restrict f))
  rw [Functor.CorepresentableBy.homEquiv_eq, restrictedTensor_identity_meaning] at h
  exact h

theorem restrictedTensor_homEquiv {P : X.Modules} (h : (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N).restrict f ⟶ P) :
    (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictedCorepresentable f M N).homEquiv h =
      ((SheafTensorMaps.tensorBilinear M N).restrict f).postcomp h := by
  rw [Functor.CorepresentableBy.homEquiv_eq, restrictedTensor_identity_meaning]
  rfl

/-- Restriction of the actual tensor map is the tensor of the restricted
maps, through the canonical sheaf comparison. -/
theorem tensorModuleRestrictIso_naturality {P Q : Y.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.restrictFunctor f).map (SheafTensorMaps.sheafTensorMap a b) ≫
      (HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso f P Q).hom =
        (HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso f M N).hom ≫
          SheafTensorMaps.sheafTensorMap ((Scheme.Modules.restrictFunctor f).map a)
            ((Scheme.Modules.restrictFunctor f).map b) := by
  apply (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrictedCorepresentable f M N).homEquiv.injective
  rw [restrictedTensor_homEquiv, restrictedTensor_homEquiv,
    HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.postcomp_comp, HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.postcomp_comp,
    ← HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrict_postcomp, SheafTensorMaps.sheafTensorMap_spec,
    HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.restrict_precomp, ← HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.precomp_postcomp,
    tensorModuleRestrictIso_bilinear, tensorModuleRestrictIso_bilinear,
    SheafTensorMaps.sheafTensorMap_spec]

end

/-! Actual tensor-frame coordinates multiply on pure section tensors,
first on the opens of a trivializing subscheme and then on ambient opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange

variable {X : Scheme.{0}} (M N : X.Modules) (U : X.Opens)
  (e : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
  (f : N.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)

def tensorFrameOnDomain : (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N).restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme :=
  HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso U.ι M N ≪≫ SheafTensorFrames.tensorSheafFrame e f

theorem tensorFrameOnImage_apply (W : U.toScheme.Opens)
    (x : Γ(M, U.ι ''ᵁ W)) (y : Γ(N, U.ι ''ᵁ W)) :
    DivisorClass.Chern.FramesFrame.Construction.frameOnImage (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) U (tensorFrameOnDomain M N U e f) W
      ((SheafTensorMaps.tensorBilinear M N).app (U.ι ''ᵁ W) x y) =
        DivisorClass.Chern.FramesFrame.Construction.frameOnImage M U e W x * DivisorClass.Chern.FramesFrame.Construction.frameOnImage N U f W y := by
  have h := congrArg
    (fun β : HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (M.restrict U.ι) (N.restrict U.ι)
      (HilbertConstruction.Tensor.ProductSheaf.tensorModule (M.restrict U.ι) (N.restrict U.ι)) => β.app W x y)
    (tensorModuleRestrictIso_bilinear U.ι M N)
  change (SheafTensorFrames.tensorSheafFrame e f).hom.app W
      ((HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso U.ι M N).hom.app W ((SheafTensorMaps.tensorBilinear M N).app (U.ι ''ᵁ W) x y)) = _
  change (HilbertConstruction.Tensor.ProductBaseChange.tensorModuleRestrictIso U.ι M N).hom.app W
    ((SheafTensorMaps.tensorBilinear M N).app (U.ι ''ᵁ W) x y) =
      (SheafTensorMaps.tensorBilinear (M.restrict U.ι) (N.restrict U.ι)).app W x y at h
  rw [h]
  exact SheafTensorFrames.tensorSheafFrame_apply e f W x y

omit U e f in
theorem tensorFrame_transport {V W : X.Opens} (h : V = W)
    (a : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V)) (b : Γ(N, V) ≃ₗ[Γ(X, V)] Γ(X, V))
    (c : Γ(HilbertConstruction.Tensor.ProductSheaf.tensorModule M N, V) ≃ₗ[Γ(X, V)] Γ(X, V))
    (hc : ∀ x y, c ((SheafTensorMaps.tensorBilinear M N).app V x y) = a x * b y)
    (x : Γ(M, W)) (y : Γ(N, W)) :
    DivisorClass.Chern.FramesFrame.Construction.transportFrame (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) h c ((SheafTensorMaps.tensorBilinear M N).app W x y) =
      DivisorClass.Chern.FramesFrame.Construction.transportFrame M h a x * DivisorClass.Chern.FramesFrame.Construction.transportFrame N h b y := by
  subst W
  exact hc x y

theorem tensorFrameOnOpen_apply (V : X.Opens) (hV : V ≤ U) (x : Γ(M, V)) (y : Γ(N, V)) :
    DivisorClass.Chern.FramesFrame.Construction.frameOnOpen (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) U (tensorFrameOnDomain M N U e f) V hV
      ((SheafTensorMaps.tensorBilinear M N).app V x y) =
        DivisorClass.Chern.FramesFrame.Construction.frameOnOpen M U e V hV x * DivisorClass.Chern.FramesFrame.Construction.frameOnOpen N U f V hV y :=
  tensorFrame_transport M N (DivisorClass.Chern.FramesFrame.Construction.image_preimage_subopen U hV)
    (DivisorClass.Chern.FramesFrame.Construction.frameOnImage M U e (U.ι ⁻¹ᵁ V)) (DivisorClass.Chern.FramesFrame.Construction.frameOnImage N U f (U.ι ⁻¹ᵁ V))
    (DivisorClass.Chern.FramesFrame.Construction.frameOnImage (HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) U (tensorFrameOnDomain M N U e f) (U.ι ⁻¹ᵁ V))
    (tensorFrameOnImage_apply M N U e f (U.ι ⁻¹ᵁ V)) x y

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.FrameCoordinates
