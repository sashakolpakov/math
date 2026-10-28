import OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusDiagonal
import OAI.AlgebraicGeometry.FormalGeometry.Completion.OpenAdjunction

/-! # Frobenius Line Bundle -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusLineBundle.Construction

noncomputable section

/-! Frobenius pullback of an actual line bundle is its cardinality tensor power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [Fintype k]
  {X : Scheme.{u}} (κ : k →+* Γ(X, ⊤)) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)

/-- The section formula of the actual Frobenius diagonal. -/
theorem lineBundleFrobeniusDiagonal_app (U : X.Opens) (s : Γ(L.sheaf, U)) :
    (FrobeniusDiagonal.Construction.lineBundleFrobeniusDiagonal k κ L).app U s =
      (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMultilinear L.sheaf (Fintype.card k)).app U (fun _ => s) := rfl

/-- Restricting actual Frobenius gives actual Frobenius on the open subscheme. -/
theorem qPowerSchemeFrobenius_restrict (U : X.Opens) :
    (Frobenius.Construction.qPowerSchemeFrobenius k X κ) ∣_ U =
      Frobenius.Construction.qPowerSchemeFrobenius k U.toScheme (U.ι.appTop.hom.comp κ) := by
  apply (cancel_mono U.ι).mp
  rw [morphismRestrict_ι]
  exact (Frobenius.Construction.qPowerSchemeFrobenius_naturality k U.toScheme
    (U.ι.appTop.hom.comp κ) κ U.ι).symm

/-- The open identification underlying Frobenius base change is the identity at the top. -/
theorem frobeniusOpenBaseChange_topOpenHom (U : X.Opens) :
    (eqToHom (image_morphismRestrict_preimage (Frobenius.Construction.qPowerSchemeFrobenius k X κ) U ⊤)).op =
      𝟙 (Opposite.op (U.ι ''ᵁ ⊤)) := Subsingleton.elim _ _

/-- The top-open identification acts identically on every abelian presheaf. -/
theorem frobeniusOpenBaseChange_presheafTop (U : X.Opens)
    (P : TopCat.Presheaf AddCommGrpCat.{u} X) (s : P.obj (Opposite.op (U.ι ''ᵁ ⊤))) :
    P.map (eqToHom (image_morphismRestrict_preimage (Frobenius.Construction.qPowerSchemeFrobenius k X κ) U ⊤)).op s = s := by
  have hp := congrArg (fun i : Opposite.op (U.ι ''ᵁ ⊤) ⟶ Opposite.op (U.ι ''ᵁ ⊤) => P.map i)
    (frobeniusOpenBaseChange_topOpenHom k κ U)
  exact (ConcreteCategory.congr_hom hp s).trans
    (ConcreteCategory.congr_hom (P.map_id (Opposite.op (U.ι ''ᵁ ⊤))) s)

/-- Open base change for actual Frobenius is the identity on top sections. -/
theorem frobeniusOpenBaseChange_appTop (U : X.Opens) (M : X.Modules)
    (s : Γ(M, U.ι ''ᵁ ⊤)) :
    @Eq Γ(M, U.ι ''ᵁ ⊤)
      (((Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap (Frobenius.Construction.qPowerSchemeFrobenius k X κ) U).app M).app ⊤ s)
      s := by
  exact (OpenAdjunction.Construction.openBaseChange_apply (Frobenius.Construction.qPowerSchemeFrobenius k X κ) U M ⊤ s).trans
    (frobeniusOpenBaseChange_presheafTop k κ U M.presheaf s)

/-- In an open frame, the diagonal carries the frame to its tensor power. -/
theorem frobeniusDiagonal_openFrame (U : X.Opens)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme ⟶ L.sheaf.restrict U.ι) :
    s ≫ (Scheme.Modules.restrictFunctor U.ι).map (FrobeniusDiagonal.Construction.lineBundleFrobeniusDiagonal k κ L) ≫
      (Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap (Frobenius.Construction.qPowerSchemeFrobenius k X κ) U).app
        (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf (Fintype.card k)) =
    SheafOfModules.unitToPushforwardObjUnit
      ((Frobenius.Construction.qPowerSchemeFrobenius k X κ) ∣_ U).toRingCatSheafHom ≫
      (Scheme.Modules.pushforward ((Frobenius.Construction.qPowerSchemeFrobenius k X κ) ∣_ U)).map
        (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection s (Fintype.card k) ≫
          (AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso U.ι L.sheaf (Fintype.card k)).hom) := by
  apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _).injective
  change ((Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap (Frobenius.Construction.qPowerSchemeFrobenius k X κ) U).app
    (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf (Fintype.card k))).app ⊤
      ((FrobeniusDiagonal.Construction.lineBundleFrobeniusDiagonal k κ L).app (U.ι ''ᵁ ⊤)
        (s.app ⊤ (1 : Γ(U.toScheme, ⊤)))) = _
  rw [frobeniusOpenBaseChange_appTop, lineBundleFrobeniusDiagonal_app]
  change _ = (AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso U.ι L.sheaf (Fintype.card k)).hom.app ⊤
    ((AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection s (Fintype.card k)).app ⊤
      (((Frobenius.Construction.qPowerSchemeFrobenius k X κ) ∣_ U).app ⊤ (1 : Γ(U.toScheme, ⊤))))
  rw [(((Frobenius.Construction.qPowerSchemeFrobenius k X κ) ∣_ U).app ⊤).hom.map_one,
    AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection_app, one_smul]
  have h := congrArg (fun β : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap (L.sheaf.restrict U.ι)
    (Fintype.card k) ((AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf (Fintype.card k)).restrict U.ι) =>
      β.app ⊤ (fun _ => s.app ⊤ (1 : Γ(U.toScheme, ⊤))))
    (AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictHom_spec U.ι L.sheaf (Fintype.card k))
  exact h.symm

/-- The global comparison is invertible, since its restriction takes each frame
to the corresponding tensor-power frame. -/
theorem lineBundleFrobeniusComparison_isIso :
    IsIso (FrobeniusDiagonal.Construction.lineBundleFrobeniusComparison k κ L) := by
  apply AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
  refine ⟨U, hx, ?_⟩
  let F := Frobenius.Construction.qPowerSchemeFrobenius k X κ
  let f := F ∣_ U
  let s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme ⟶ L.sheaf.restrict U.ι :=
    e.inv ≫ ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf).inv
  have : IsIso s := by dsimp [s]; infer_instance
  let t := AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection s (Fintype.card k) ≫
    (AbelianModuli.HilbertConstruction.TensorPower.RestrictionMaps.tensorPowerRestrictIso U.ι L.sheaf (Fintype.card k)).hom
  have : IsIso t := by dsimp [t]; infer_instance
  let a := (Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare F U).hom.app L.sheaf ≫
    (Scheme.Modules.restrictFunctor U.ι).map (FrobeniusDiagonal.Construction.lineBundleFrobeniusComparison k κ L)
  have he : (Scheme.Modules.pullback f).map s ≫ a =
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ t := by
    have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
    apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left]
    have hu : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
        SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
    have ht : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
        ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ t) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map t :=
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom t).trans
          (congrArg (fun z => z ≫ (Scheme.Modules.pushforward f).map t) hu)
    rw [ht]
    have hc := OpenAdjunction.Construction.openRestriction_homEquiv F U (FrobeniusDiagonal.Construction.lineBundleFrobeniusComparison k κ L)
    have hdiag : ((Scheme.Modules.pullbackPushforwardAdjunction F).homEquiv _ _)
        (FrobeniusDiagonal.Construction.lineBundleFrobeniusComparison k κ L) = FrobeniusDiagonal.Construction.lineBundleFrobeniusDiagonal k κ L :=
      Equiv.apply_symm_apply _ _
    rw [hdiag] at hc
    rw [show ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _) a = _ from hc]
    exact frobeniusDiagonal_openFrame k κ L U s
  have : IsIso ((Scheme.Modules.pullback f).map s ≫ a) := he.symm ▸ inferInstance
  have : IsIso a := (isIso_comp_left_iff _ _).mp this
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (FrobeniusDiagonal.Construction.lineBundleFrobeniusComparison k κ L)) := (isIso_comp_left_iff _ _).mp this
  exact (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff U.ι _).mp this

/-- The actual global Frobenius pullback isomorphism for every line bundle. -/
def lineBundleFrobeniusIso :
    (Scheme.Modules.pullback (Frobenius.Construction.qPowerSchemeFrobenius k X κ)).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L.sheaf (Fintype.card k) :=
  @asIso X.Modules _ _ _ (FrobeniusDiagonal.Construction.lineBundleFrobeniusComparison k κ L)
    (lineBundleFrobeniusComparison_isIso k κ L)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FrobeniusLineBundle.Construction
