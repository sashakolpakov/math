import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenPullbackSections

/-! # Pullback Section Compatibility -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionCompatibility.Construction

noncomputable section

/-! Restriction and composition laws for the canonical pullback of module sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

def modulePullbackSectionLE (U : Y.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) :
    Γ(M, U) →+ Γ((Scheme.Modules.pullback f).obj M, V) :=
  (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hVU).op).hom.comp
    (OpenPullbackSections.Construction.modulePullbackSection f M U)

theorem modulePullbackSectionLE_smul (U : Y.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
    (r : Γ(Y, U)) (m : Γ(M, U)) :
    modulePullbackSectionLE f M U V hVU (r • m) =
      f.appLE U V hVU r • modulePullbackSectionLE f M U V hVU m := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hVU).op
    (OpenPullbackSections.Construction.modulePullbackSection f M U (r • m)) = _
  rw [OpenPullbackSections.Construction.modulePullbackSection_smul, Scheme.Modules.map_smul]
  rfl

theorem modulePullbackSection_naturality {N : Y.Modules} (q : M ⟶ N)
    (U : Y.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map q).app (f ⁻¹ᵁ U) (OpenPullbackSections.Construction.modulePullbackSection f M U m) =
      OpenPullbackSections.Construction.modulePullbackSection f N U (q.app U m) :=
  (congrArg (fun t : M ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj N) ↦
    t.app U m) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality q)).symm

theorem modulePullbackSection_restrict {U V : Y.Opens} (i : V ⟶ U) (m : Γ(M, U)) :
    OpenPullbackSections.Construction.modulePullbackSection f M V (M.presheaf.map i.op m) =
      ((Scheme.Modules.pullback f).obj M).presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op
        (OpenPullbackSections.Construction.modulePullbackSection f M U m) := by
  exact congrArg (fun q : Γ(M, U) ⟶ Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ V) ↦ q m)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality i.op)

theorem modulePullbackSectionLE_naturality {N : Y.Modules} (q : M ⟶ N)
    (U : Y.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((Scheme.Modules.pullback f).map q).app V (modulePullbackSectionLE f M U V hVU m) =
      modulePullbackSectionLE f N U V hVU (q.app U m) := by
  have h := congrArg (fun t : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) ⟶
      Γ((Scheme.Modules.pullback f).obj N, V) ↦ t (OpenPullbackSections.Construction.modulePullbackSection f M U m))
    (((Scheme.Modules.pullback f).map q).mapPresheaf.naturality (homOfLE hVU).op)
  change ((Scheme.Modules.pullback f).map q).app V (modulePullbackSectionLE f M U V hVU m) =
    ((Scheme.Modules.pullback f).obj N).presheaf.map (homOfLE hVU).op
      (((Scheme.Modules.pullback f).map q).app (f ⁻¹ᵁ U) (OpenPullbackSections.Construction.modulePullbackSection f M U m)) at h
  rw [h, modulePullbackSection_naturality]
  rfl

theorem modulePullbackSectionLE_restrict {U V : Y.Opens} (i : V ⟶ U)
    {U' V' : X.Opens} (j : V' ⟶ U') (hU : U' ≤ f ⁻¹ᵁ U) (hV : V' ≤ f ⁻¹ᵁ V)
    (m : Γ(M, U)) :
    modulePullbackSectionLE f M V V' hV (M.presheaf.map i.op m) =
      ((Scheme.Modules.pullback f).obj M).presheaf.map j.op
        (modulePullbackSectionLE f M U U' hU m) := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hV).op
    (OpenPullbackSections.Construction.modulePullbackSection f M V (M.presheaf.map i.op m)) = _
  rw [modulePullbackSection_restrict]
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hV).op
    (((Scheme.Modules.pullback f).obj M).presheaf.map
      ((TopologicalSpace.Opens.map f.base).map i).op (OpenPullbackSections.Construction.modulePullbackSection f M U m)) =
    ((Scheme.Modules.pullback f).obj M).presheaf.map j.op
      (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hU).op
        (OpenPullbackSections.Construction.modulePullbackSection f M U m))
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem modulePullbackSection_comp (g : Y ⟶ Z) (N : Z.Modules) (U : Z.Opens) (m : Γ(N, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app N).app ((f ≫ g) ⁻¹ᵁ U)
      (OpenPullbackSections.Construction.modulePullbackSection f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U)
        (OpenPullbackSections.Construction.modulePullbackSection g N U m)) = OpenPullbackSections.Construction.modulePullbackSection (f ≫ g) N U m := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv N
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have hs := congrArg (fun q : N ⟶ (Scheme.Modules.pushforward (f ≫ g)).obj
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)) ↦ q.app U m) h
  change OpenPullbackSections.Construction.modulePullbackSection f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U)
    (OpenPullbackSections.Construction.modulePullbackSection g N U m) =
      ((Scheme.Modules.pullbackComp f g).inv.app N).app ((f ≫ g) ⁻¹ᵁ U)
        (OpenPullbackSections.Construction.modulePullbackSection (f ≫ g) N U m) at hs
  rw [hs]
  exact congrArg (fun q : (Scheme.Modules.pullback (f ≫ g)).obj N ⟶
      (Scheme.Modules.pullback (f ≫ g)).obj N ↦ q.app ((f ≫ g) ⁻¹ᵁ U)
        (OpenPullbackSections.Construction.modulePullbackSection (f ≫ g) N U m)) ((Scheme.Modules.pullbackComp f g).app N).inv_hom_id

theorem modulePullbackSectionLE_comp (g : Y ⟶ Z) (N : Z.Modules)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ f ⁻¹ᵁ V)
    (m : Γ(N, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app N).app W
      (modulePullbackSectionLE f ((Scheme.Modules.pullback g).obj N) V W hW
        (modulePullbackSectionLE g N U V hV m)) =
      modulePullbackSectionLE (f ≫ g) N U W (hW.trans (f.preimage_mono hV)) m := by
  have hr := modulePullbackSectionLE_restrict f ((Scheme.Modules.pullback g).obj N)
    (homOfLE hV) (𝟙 W) (hW.trans (f.preimage_mono hV)) hW (OpenPullbackSections.Construction.modulePullbackSection g N U m)
  have hid (x : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), W)) :
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)).presheaf.map (𝟙 W).op x = x :=
    congrArg (fun q : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), W) ⟶
      Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), W) ↦ q x)
        (((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)).presheaf.map_id (op W))
  have hr := hr.trans (hid _)
  change modulePullbackSectionLE f ((Scheme.Modules.pullback g).obj N) V W hW
    (modulePullbackSectionLE g N U V hV m) = _ at hr
  rw [hr]
  have hn := congrArg (fun q :
      Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), (f ≫ g) ⁻¹ᵁ U) ⟶
      Γ((Scheme.Modules.pullback (f ≫ g)).obj N, W) ↦
        q (OpenPullbackSections.Construction.modulePullbackSection f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U)
          (OpenPullbackSections.Construction.modulePullbackSection g N U m)))
    (((Scheme.Modules.pullbackComp f g).hom.app N).mapPresheaf.naturality
      (homOfLE (hW.trans (f.preimage_mono hV))).op)
  change ((Scheme.Modules.pullbackComp f g).hom.app N).app W
    (modulePullbackSectionLE f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U) W
      (hW.trans (f.preimage_mono hV)) (OpenPullbackSections.Construction.modulePullbackSection g N U m)) =
    ((Scheme.Modules.pullback (f ≫ g)).obj N).presheaf.map
      (homOfLE (hW.trans (f.preimage_mono hV))).op
        (((Scheme.Modules.pullbackComp f g).hom.app N).app ((f ≫ g) ⁻¹ᵁ U)
          (OpenPullbackSections.Construction.modulePullbackSection f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U)
            (OpenPullbackSections.Construction.modulePullbackSection g N U m))) at hn
  rw [hn, modulePullbackSection_comp]
  rfl

theorem modulePullbackSectionLE_congr {g : X ⟶ Y} (hfg : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr hfg).hom.app M).app V
      (modulePullbackSectionLE f M U V hf m) = modulePullbackSectionLE g M U V hg m := by
  subst g
  rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionCompatibility.Construction
