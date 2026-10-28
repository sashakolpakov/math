import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleDual

/-! # Sheafification Local Iso -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafificationLocalIso.Construction

noncomputable section

/-! Detecting invertibility of a sheafified map on local module charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def moduleSheafificationLift {X : Scheme.{u}} {P : X.PresheafOfModules} {N : X.Modules}
    (q : P ⟶ N.val) : SheafTensor.Construction.sheafifyModule P ⟶ N :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm q

theorem moduleSheafificationUnit_lift {X : Scheme.{u}} {P : X.PresheafOfModules} {N : X.Modules}
    (q : P ⟶ N.val) : SheafRestriction.Construction.moduleSheafificationUnit P ≫ (moduleSheafificationLift q).val = q := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  exact (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply q)

theorem moduleSheafificationLift_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {P : Y.PresheafOfModules} {N : Y.Modules} (q : P ⟶ N.val) :
    (SheafRestriction.Construction.restrictSheafificationIso f P).hom ≫ (Scheme.Modules.restrictFunctor f).map
        (moduleSheafificationLift q) =
      @moduleSheafificationLift X _ (N.restrict f) ((SheafRestriction.Construction.restrictModulePresheaf f).map q) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let R := SheafRestriction.Construction.restrictModulePresheaf f
  apply (adj.homEquiv _ _).injective
  have hunit := TensorOpenComparison.Construction.moduleSheafificationUnit_restrictIso f P
  have hmap : R.map (SheafRestriction.Construction.moduleSheafificationUnit P) ≫ R.map (moduleSheafificationLift q).val = R.map q :=
    (R.map_comp _ _).symm.trans (congrArg R.map (moduleSheafificationUnit_lift q))
  have hcomp : SheafRestriction.Construction.moduleSheafificationUnit (R.obj P) ≫
      ((SheafRestriction.Construction.restrictSheafificationIso f P).hom ≫ (Scheme.Modules.restrictFunctor f).map
        (moduleSheafificationLift q)).val = R.map q :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a ↦ a ≫ R.map (moduleSheafificationLift q).val) hunit).trans hmap)
  exact (adj.homEquiv_unit _ _ _).trans
    (hcomp.trans ((adj.homEquiv (R.obj P) (N.restrict f)).apply_symm_apply (R.map q)).symm)

theorem isIso_moduleSheafificationLift {X : Scheme.{u}} {P : X.PresheafOfModules} {N : X.Modules}
    (q : P ⟶ N.val) [IsIso q] : IsIso (moduleSheafificationLift q) := by
  let F : X.PresheafOfModules ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have he : moduleSheafificationLift q = F.map q ≫ (SheafTensor.Construction.sheafifyModuleIso N).hom :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_counit _ _ q
  rw [he]
  exact IsIso.comp_isIso' (inferInstanceAs (IsIso (F.map q))) (SheafTensor.Construction.sheafifyModuleIso N).isIso_hom

theorem isIso_restrictModulePresheaf_map_of_app {X : Scheme.{u}}
    {P Q : X.PresheafOfModules} (q : P ⟶ Q) (U : X.Opens)
    (hq : ∀ V : X.Opens, V ≤ U → IsIso (q.app (.op V))) :
    IsIso ((SheafRestriction.Construction.restrictModulePresheaf U.ι).map q) := by
  let r := (SheafRestriction.Construction.restrictModulePresheaf U.ι).map q
  have hi (V : U.toScheme.Opensᵒᵖ) : IsIso (r.app V) := by
    let e := @asIso _ _ _ _ (q.app (.op (U.ι ''ᵁ V.unop)))
      (hq (U.ι ''ᵁ V.unop) (U.ι_image_le V.unop))
    exact ((ModuleCat.restrictScalars ((U.ι.appIso V.unop).inv).hom).mapIso
      e).isIso_hom
  let e := PresheafOfModules.isoMk (fun V ↦ asIso (r.app V)) (fun _ _ h ↦ r.naturality h)
  exact e.isIso_hom

theorem isIso_moduleSheafificationLift_of_local_app {X : Scheme.{u}}
    {P : X.PresheafOfModules} {N : X.Modules} (q : P ⟶ N.val)
    (hq : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∀ V : X.Opens, V ≤ U → IsIso (q.app (.op V))) :
    IsIso (moduleSheafificationLift q) := by
  apply ModuleLocalIso.Construction.isIso_of_locally_isIso_pullback
  intro x
  obtain ⟨U, hxU, hU⟩ := hq x
  have hR := isIso_restrictModulePresheaf_map_of_app q U hU
  have := @isIso_moduleSheafificationLift U.toScheme _ (N.restrict U.ι)
    ((SheafRestriction.Construction.restrictModulePresheaf U.ι).map q) hR
  have : IsIso ((SheafRestriction.Construction.restrictSheafificationIso U.ι P).hom ≫
      (Scheme.Modules.restrictFunctor U.ι).map (moduleSheafificationLift q)) := by
    rw [moduleSheafificationLift_restrict]
    infer_instance
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (moduleSheafificationLift q)) :=
    IsIso.of_isIso_comp_left (SheafRestriction.Construction.restrictSheafificationIso U.ι P).hom _
  exact ⟨U, hxU, LineBundlePullbackUnit.Construction.isIso_pullbackMap_of_restrictMap U.ι _⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafificationLocalIso.Construction
