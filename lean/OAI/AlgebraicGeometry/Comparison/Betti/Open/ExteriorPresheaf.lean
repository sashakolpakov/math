import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves

/-! # Exterior Presheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ExteriorPresheaf

noncomputable section

section

/-! The actual open-image section isomorphism respects complex scalars and restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

attribute [local instance] Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

def openImageSectionAlgHom (U : X.left.Opens) :
    Γ(Y.left, f.left ''ᵁ U) →ₐ[ℂ] Γ(X.left, U) where
  __ := (f.left.appIso U).hom.hom
  commutes' c := by
    have h := Scheme.Hom.appLE_comp_appLE f.left Y.hom ⊤ (f.left ''ᵁ U) U le_top
      (f.left.preimage_image_eq U).ge
    rw [← f.left.appIso_hom'] at h
    have hw := congrArg (fun g : X.left ⟶ Foundations.Scheme.ProjectiveSpace.complexBase => g.appLE ⊤ U le_top) (Over.w f)
    exact ConcreteCategory.congr_hom (h.trans hw) ((Scheme.ΓSpecIso (.of ℂ)).inv c)

def openImageSectionAlgEquiv (U : X.left.Opens) :
    Γ(Y.left, f.left ''ᵁ U) ≃ₐ[ℂ] Γ(X.left, U) :=
  AlgEquiv.ofBijective (openImageSectionAlgHom f U)
    (ConcreteCategory.bijective_of_isIso (f.left.appIso U).hom)

theorem openImageSectionAlgHom_naturality {U V : X.left.Opensᵒᵖ} (i : U ⟶ V) :
    (openImageSectionAlgHom f V.unop).comp
        (((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ Y).map
          (f.left.opensFunctor.op.map i)).hom) =
      (((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).map i).hom).comp
        (openImageSectionAlgHom f U.unop) := by
  ext a
  exact ConcreteCategory.congr_hom (f.left.appIso_hom_naturality i) a

end

/-! Restriction of the actual exterior-form presheaves, with their full coefficient actions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham

attribute [local instance] Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

def openRestrictionRingHom : X.left.ringCatSheaf ⟶
    (f.left.opensFunctor.sheafPushforwardContinuous RingCat.{0}
      (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology Y.left)).obj
        Y.left.ringCatSheaf := by
  let α : X.left.presheaf ⟶ f.left.opensFunctor.op ⋙ Y.left.presheaf :=
    { app U := (f.left.appIso U.unop).inv
      naturality U V i := f.left.appIso_inv_naturality i }
  exact ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

def restrictedExteriorModulePresheaf (n : ℕ) : X.left.PresheafOfModules :=
  (PresheafOfModules.pushforward (openRestrictionRingHom f).hom).obj
    (Exterior.ModuleSheaf.exteriorFormsModulePresheaf Y n)

def exteriorOpenModuleMap (n : ℕ) (U : X.left.Opensᵒᵖ) :
    (restrictedExteriorModulePresheaf f n).obj U ⟶
      (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n).obj U :=
  ModuleCat.ofHom (X := (restrictedExteriorModulePresheaf f n).obj U)
    (Y := (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n).obj U)
    { toFun := Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.ofHom (openImageSectionAlgHom f U.unop)) n
      map_add' := by intros; exact map_add _ _ _
      map_smul' a ω := by
        change Γ(X.left, U.unop) at a
        change Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (CommAlgCat.of ℂ Γ(Y.left, f.left ''ᵁ U.unop)) n at ω
        change Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.ofHom (openImageSectionAlgHom f U.unop)) n
            ((f.left.appIso U.unop).inv a • ω) =
          a • Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.ofHom (openImageSectionAlgHom f U.unop)) n ω
        erw [Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_smul]
        congr 1
        exact ConcreteCategory.congr_hom (f.left.appIso U.unop).inv_hom_id a }

theorem exteriorOpenModuleMap_isIso (n : ℕ) (U : X.left.Opensᵒᵖ) :
    IsIso (exteriorOpenModuleMap f n U) := by
  let e := (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsFunctor (R := ℂ) n).mapIso
    (CommAlgCat.isoMk (openImageSectionAlgEquiv f U.unop))
  apply (ConcreteCategory.isIso_iff_bijective (exteriorOpenModuleMap f n U)).mpr
  exact ConcreteCategory.bijective_of_isIso e.hom

theorem exteriorOpenModuleMap_naturality (n : ℕ) {U V : X.left.Opensᵒᵖ} (i : U ⟶ V) :
    (restrictedExteriorModulePresheaf f n).map i ≫
        (ModuleCat.restrictScalars (X.left.ringCatSheaf.obj.map i).hom).map
          (exteriorOpenModuleMap f n V) =
      exteriorOpenModuleMap f n U ≫ (Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n).map i := by
  apply ConcreteCategory.hom_ext
  intro ω
  change Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.ofHom (openImageSectionAlgHom f V.unop)) n
      (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap ((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ Y).map (f.left.opensFunctor.op.map i)) n ω) =
    Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap ((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).map i) n
      (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (CommAlgCat.ofHom (openImageSectionAlgHom f U.unop)) n ω)
  erw [← Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_comp, ← Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_comp]
  have h : (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ Y).map (f.left.opensFunctor.op.map i) ≫
      CommAlgCat.ofHom (openImageSectionAlgHom f V.unop) =
    CommAlgCat.ofHom (openImageSectionAlgHom f U.unop) ≫ (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).map i := by
    apply CommAlgCat.hom_ext
    exact openImageSectionAlgHom_naturality f i
  erw [h]
  rfl

def exteriorOpenPresheafIso (n : ℕ) :
    restrictedExteriorModulePresheaf f n ≅ Exterior.ModuleSheaf.exteriorFormsModulePresheaf X n := by
  have (U : X.left.Opensᵒᵖ) : IsIso (exteriorOpenModuleMap f n U) :=
    exteriorOpenModuleMap_isIso f n U
  exact PresheafOfModules.isoMk (fun U => asIso (exteriorOpenModuleMap f n U))
    (fun {_ _} i => exteriorOpenModuleMap_naturality f n i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ExteriorPresheaf
