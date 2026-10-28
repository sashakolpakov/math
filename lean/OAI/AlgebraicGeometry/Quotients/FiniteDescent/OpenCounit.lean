import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenPullbackIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructurePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

/-! # Open Counit -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCounit

noncomputable section

/-! A module locally trivial over opens of the base descends along a
morphism whose structure sheaf has constant direct image. The adjunction
counit gives the global descent isomorphism. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms

universe u

namespace Construction.OpenCounitDescent

variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem structure_counit
    [IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)] :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have ht : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have he := congrArg ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm ht
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at he
  have : IsIso ((Scheme.Modules.pullback f).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((Scheme.Modules.pullback f).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))

theorem trivial_counit
    [IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)]
    (M : X.Modules) (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  have := structure_counit f
  have he := (Scheme.Modules.pullbackPushforwardAdjunction f).counit.naturality e.hom
  change (Scheme.Modules.pullback f).map ((Scheme.Modules.pushforward f).map e.hom) ≫
    (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) =
    (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M ≫ e.hom at he
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M ≫ e.hom) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_right
    ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) e.hom

theorem counit_square (U : S.Opens) (M : X.Modules) :
    (Scheme.Modules.pullback (f ∣_ U)).map ((OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap f U).app M) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).counit.app
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M) =
    (OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  have h := mateEquiv_counit (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (TwoSquare.mk _ _ _ _ (OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U).hom) M
  change (Scheme.Modules.pullback (f ∣_ U)).map ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (TwoSquare.mk _ _ _ _ (OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U).hom)).natTrans.app M) ≫ _ = _ at h
  rw [OpenPullbackIs.Construction.OpenPullbackSquare.rightMate] at h
  exact h

theorem restricted_counit (U : S.Opens)
    [IsIso (SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom)]
    (M : X.Modules)
    (e : (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (f ⁻¹ᵁ U).toScheme) :
    IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) := by
  have := trivial_counit (f ∣_ U) ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)
    ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app M ≪≫ e)
  have := OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap_isIso f U
  have : IsIso ((OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U).hom.app
      ((Scheme.Modules.pushforward f).obj M) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) := by
    rw [← counit_square]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U).hom.app ((Scheme.Modules.pushforward f).obj M))
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M))

theorem counit (M : X.Modules)
    (hO : ∀ U : S.Opens,
      IsIso (SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom))
    (hn : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ Nonempty
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (f ⁻¹ᵁ U).toScheme)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  apply AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := hn (f x)
  have := hO U
  have hi := restricted_counit f U M e
  exact ⟨f ⁻¹ᵁ U, hx, (AbelianModuli.HilbertConstruction.Power.Nonvanishing.isIso_restrict_map_iff (f ⁻¹ᵁ U).ι _).mp hi⟩

end Construction.OpenCounitDescent

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCounit
