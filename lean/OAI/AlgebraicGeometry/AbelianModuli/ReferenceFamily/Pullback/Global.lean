import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorFrames
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackScalars

/-! # Global -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.Global

noncomputable section

section

/-! Actual pullback frames and their regular transition functions. The
section formula follows from the pullback/pushforward adjunction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {M : Y.Modules}

def pullbackGlobalFrame (e : M ≅ HilbertConstruction.Line.Bundles.structureModule Y) :
    (Scheme.Modules.pullback f).obj M ≅ HilbertConstruction.Line.Bundles.structureModule X :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ HilbertConstruction.Line.Bundles.structureModulePullbackIso f

theorem pullbackGlobalFrame_adjunction (e : M ≅ HilbertConstruction.Line.Bundles.structureModule Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackGlobalFrame f e).hom =
    e.hom ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  unfold pullbackGlobalFrame
  rw [Iso.trans_hom, Functor.mapIso_hom, Adjunction.homEquiv_naturality_left]
  exact congrArg (fun a => e.hom ≫ a)
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom)

theorem pullbackGlobalFrame_sections (e : M ≅ HilbertConstruction.Line.Bundles.structureModule Y) (U : Y.Opens)
    (m : Γ(M, U)) :
    SheafTensorFrames.sheafSectionFrame (pullbackGlobalFrame f e) (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m) =
      f.app U (SheafTensorFrames.sheafSectionFrame e U m) := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun a : M ⟶ (Scheme.Modules.pushforward f).obj (HilbertConstruction.Line.Bundles.structureModule X) => a.app U)
      (pullbackGlobalFrame_adjunction f e)) m

theorem pullbackGlobalFrame_transition (e d : M ≅ HilbertConstruction.Line.Bundles.structureModule Y) (U : Y.Opens) :
    Units.map (f.app U).hom.toMonoidHom
      (DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (SheafTensorFrames.sheafSectionFrame e U) (SheafTensorFrames.sheafSectionFrame d U)) =
    DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit (SheafTensorFrames.sheafSectionFrame (pullbackGlobalFrame f e) (f ⁻¹ᵁ U))
      (SheafTensorFrames.sheafSectionFrame (pullbackGlobalFrame f d) (f ⁻¹ᵁ U)) :=
  DivisorClass.Chern.FramesFrame.Construction.frameTransitionUnit_map
    (N := Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U)) (f.app U).hom
    (fun m => ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m)
    _ _ _ _ (pullbackGlobalFrame_sections f e U) (pullbackGlobalFrame_sections f d U)

end

section

/-! The canonical pullback comparisons carry the actual section maps
from their adjunction units. These formulas keep track of all local
frame transports without assuming compatibility of chosen frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open Scheme.Modules

variable {X Y Z : Scheme.{0}}

def pullbackSectionMap (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) → Γ((pullback f).obj M, f ⁻¹ᵁ U) :=
  fun m => ((pullbackPushforwardAdjunction f).unit.app M).app U m

theorem pullbackComp_inv_section (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (m : Γ(M, U)) :
    ((pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (pullbackSectionMap (f ≫ g) M U m) =
    pullbackSectionMap f ((pullback g).obj M) (g ⁻¹ᵁ U)
      (pullbackSectionMap g M U m) := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  exact (ConcreteCategory.congr_hom
    (congrArg (fun a => a.app U) h) m).symm

theorem pullbackComp_hom_section (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (m : Γ(M, U)) :
    ((pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (pullbackSectionMap f ((pullback g).obj M) (g ⁻¹ᵁ U)
        (pullbackSectionMap g M U m)) = pullbackSectionMap (f ≫ g) M U m := by
  rw [← pullbackComp_inv_section]
  exact ConcreteCategory.congr_hom
    (congrArg (fun a => a.app ((f ≫ g) ⁻¹ᵁ U))
      ((pullbackComp f g).app M).inv_hom_id) _

theorem restrictionPullback_hom_section (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    ((restrictFunctorIsoPullback f).hom.app M).app (f ⁻¹ᵁ U)
      (M.presheaf.map (homOfLE (f.image_preimage_le U)).op m) =
    pullbackSectionMap f M U m := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (restrictAdjunction f) (pullbackPushforwardAdjunction f) M
  exact ConcreteCategory.congr_hom (congrArg (fun a => a.app U) h) m

theorem restrictionPullback_inv_section (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    ((restrictFunctorIsoPullback f).inv.app M).app (f ⁻¹ᵁ U)
      (pullbackSectionMap f M U m) =
    M.presheaf.map (homOfLE (f.image_preimage_le U)).op m := by
  rw [← restrictionPullback_hom_section]
  exact ConcreteCategory.congr_hom
    (congrArg (fun a => a.app (f ⁻¹ᵁ U))
      ((restrictFunctorIsoPullback f).app M).hom_inv_id) _

end

/-! Pullback section maps restricted to arbitrary smaller source opens,
with their functorial composition and open-immersion formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open Scheme.Modules

variable {X Y Z : Scheme.{0}}

theorem moduleHom_restrict {M N : X.Modules} (a : M ⟶ N) {U W : X.Opens}
    (h : W ≤ U) (m : Γ(M, U)) :
    a.app W (M.presheaf.map (homOfLE h).op m) =
      N.presheaf.map (homOfLE h).op (a.app U m) :=
  ConcreteCategory.congr_hom (a.mapPresheaf.naturality (homOfLE h).op) m

def pullbackSectionMapLE (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) : Γ(M, U) → Γ((pullback f).obj M, W) :=
  fun m => ((pullback f).obj M).presheaf.map (homOfLE h).op (pullbackSectionMap f M U m)

theorem pullbackSectionMapLE_self (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (m : Γ(M, U)) :
    pullbackSectionMapLE f M U (f ⁻¹ᵁ U) le_rfl m = pullbackSectionMap f M U m := by
  exact ConcreteCategory.congr_hom (((pullback f).obj M).presheaf.map_id _) _

theorem pullbackGlobalFrame_sectionsLE (f : X ⟶ Y) {M : Y.Modules}
    (e : M ≅ HilbertConstruction.Line.Bundles.structureModule Y) (U : Y.Opens) (W : X.Opens)
    (h : W ≤ f ⁻¹ᵁ U) (m : Γ(M, U)) :
    (pullbackGlobalFrame f e).hom.app W (pullbackSectionMapLE f M U W h m) =
      f.appLE U W h (e.hom.app U m) := by
  unfold pullbackSectionMapLE
  exact (moduleHom_restrict (pullbackGlobalFrame f e).hom h _).trans
    (congrArg (X.presheaf.map (homOfLE h).op) (pullbackGlobalFrame_sections f e U m))

theorem pullbackSectionMapLE_morphism (f : X ⟶ Y) {M N : Y.Modules} (a : M ⟶ N)
    (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((pullback f).map a).app W (pullbackSectionMapLE f M U W h m) =
      pullbackSectionMapLE f N U W h (a.app U m) := by
  unfold pullbackSectionMapLE
  rw [moduleHom_restrict]
  exact congrArg (((pullback f).obj N).presheaf.map (homOfLE h).op)
    (ConcreteCategory.congr_hom
      (congrArg (fun q => q.app U) ((pullbackPushforwardAdjunction f).unit.naturality a)) m).symm

theorem pullbackComp_inv_sectionLE (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (W : X.Opens) (h : W ≤ (f ≫ g) ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((pullbackComp f g).inv.app M).app W (pullbackSectionMapLE (f ≫ g) M U W h m) =
    pullbackSectionMapLE f ((pullback g).obj M) (g ⁻¹ᵁ U) W h
      (pullbackSectionMap g M U m) := by
  unfold pullbackSectionMapLE
  exact (moduleHom_restrict ((pullbackComp f g).inv.app M) h _).trans
    (congrArg (((pullback f).obj ((pullback g).obj M)).presheaf.map (homOfLE h).op)
      (pullbackComp_inv_section f g M U m))

theorem pullbackComp_hom_sectionLE (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (W : X.Opens) (h : W ≤ (f ≫ g) ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((pullbackComp f g).hom.app M).app W
      (pullbackSectionMapLE f ((pullback g).obj M) (g ⁻¹ᵁ U) W h
        (pullbackSectionMap g M U m)) = pullbackSectionMapLE (f ≫ g) M U W h m := by
  rw [← pullbackComp_inv_sectionLE]
  exact ConcreteCategory.congr_hom
    (congrArg (fun a => a.app W) ((pullbackComp f g).app M).inv_hom_id) _

theorem pullbackCongr_hom_sectionLE {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules)
    (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((pullbackCongr hf).hom.app M).app W (pullbackSectionMapLE f M U W h m) =
      pullbackSectionMapLE g M U W h' m := by
  subst g
  rfl

theorem restrictionPullback_hom_sectionLE (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((restrictFunctorIsoPullback f).hom.app M).app W
      (M.presheaf.map (homOfLE ((f.image_mono h).trans (f.image_preimage_le U))).op m) =
    pullbackSectionMapLE f M U W h m := by
  unfold pullbackSectionMapLE
  rw [← restrictionPullback_hom_section f M U m]
  exact (congrArg (((restrictFunctorIsoPullback f).hom.app M).app W)
    (ConcreteCategory.congr_hom (M.presheaf.map_comp
      (homOfLE (f.image_preimage_le U)).op (homOfLE (f.image_mono h)).op) m)).trans
    (moduleHom_restrict ((restrictFunctorIsoPullback f).hom.app M) h _)

theorem restrictionPullback_inv_sectionLE (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((restrictFunctorIsoPullback f).inv.app M).app W
      (pullbackSectionMapLE f M U W h m) =
    M.presheaf.map (homOfLE ((f.image_mono h).trans (f.image_preimage_le U))).op m := by
  rw [← restrictionPullback_hom_sectionLE]
  exact ConcreteCategory.congr_hom
    (congrArg (fun a => a.app W) ((restrictFunctorIsoPullback f).app M).hom_inv_id) _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.Global
