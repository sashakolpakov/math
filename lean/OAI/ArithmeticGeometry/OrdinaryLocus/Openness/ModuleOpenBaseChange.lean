import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleTensorPullback

/-! # Module Open Base Change -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleOpenBaseChange.Construction

noncomputable section

/-! Pushforward of module sheaves commutes with restriction to open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def moduleOpenBaseChangeAppIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (M : X.Modules) (V : U.toScheme.Opens) :
    (((Scheme.Modules.pushforward f).obj M).restrict U.ι).val.obj (.op V) ≅
      ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι)).val.obj (.op V) := by
  refine ModuleCat.isoMk (M.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U V)).op) ?_
  intro a
  ext m
  let a' : Γ(Y, U.ι ''ᵁ V) := (U.ι.appIso V).inv a
  let m' : Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) := m
  let b : Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) :=
    ((f ⁻¹ᵁ U).ι.appIso ((f ∣_ U) ⁻¹ᵁ V)).inv ((f ∣_ U).app V a)
  change b •
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op m' =
    M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op
      (f.app (U.ι ''ᵁ V) a' • m')
  have hb : b = X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op
      (f.app (U.ι ''ᵁ V) a') :=
    by
      dsimp only [a', b]
      rw [Scheme.Opens.ι_appIso, Scheme.Opens.ι_appIso]
      change (f ∣_ U).app V a =
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op
          (f.app (U.ι ''ᵁ V) a)
      exact congrArg (fun q ↦ q a) (morphismRestrict_app f U V)
  exact (congrArg (fun c ↦ c •
    M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op m') hb).trans
      (Scheme.Modules.map_smul M _ _ _).symm

def moduleOpenBaseChangePresheafIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (M : X.Modules) :
    (((Scheme.Modules.pushforward f).obj M).restrict U.ι).val ≅
      ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι)).val := by
  let A : U.toScheme.PresheafOfModules :=
    (((Scheme.Modules.pushforward f).obj M).restrict U.ι).val
  let B : U.toScheme.PresheafOfModules :=
    ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι)).val
  refine PresheafOfModules.isoMk (M₁ := A) (M₂ := B)
    (fun V ↦ moduleOpenBaseChangeAppIso f U M V.unop) ?_
  intro V W h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
      (M.presheaf.map ((TopologicalSpace.Opens.map f.base).map
        (U.ι.opensFunctor.map h.unop)).op m) =
    M.presheaf.map ((f ⁻¹ᵁ U).ι.opensFunctor.map
      ((TopologicalSpace.Opens.map (f ∣_ U).base).map h.unop)).op
      (M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op m)
  let i := ((TopologicalSpace.Opens.map f.base).map (U.ι.opensFunctor.map h.unop)).op
  let j := ((f ⁻¹ᵁ U).ι.opensFunctor.map
    ((TopologicalSpace.Opens.map (f ∣_ U).base).map h.unop)).op
  let eV := (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
  let eW := (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
  have he : i ≫ eW = eV ≫ j := Subsingleton.elim _ _
  have hm : M.presheaf.map i ≫ M.presheaf.map eW =
      M.presheaf.map eV ≫ M.presheaf.map j :=
    (M.presheaf.map_comp i eW).symm.trans
      ((congrArg M.presheaf.map he).trans (M.presheaf.map_comp eV j))
  exact congrArg (fun a ↦ a m) hm

def moduleOpenBaseChangeIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := U.toScheme)).preimageIso
    (moduleOpenBaseChangePresheafIso f U M)

theorem moduleOpenBaseChangeIso_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (M : X.Modules) (V : U.toScheme.Opens) :
    (moduleOpenBaseChangeIso f U M).hom.app V =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := rfl

def moduleOpenBaseChangeNatIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward (f ∣_ U) := by
  refine NatIso.ofComponents (moduleOpenBaseChangeIso f U) ?_
  intro M N q
  apply Scheme.Modules.hom_ext
  intro V
  simp only [Scheme.Modules.Hom.comp_app, moduleOpenBaseChangeIso_hom_app]
  exact (q.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U V)).op).symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleOpenBaseChange.Construction
