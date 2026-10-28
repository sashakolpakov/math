import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenModule
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Open Pullback Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenPullbackIs

noncomputable section

/-!
# The adjunction base-change map for open subsets

The commutative square of scheme morphisms gives an isomorphism of
composed direct images. Taking its mate across the two open-restriction
adjunctions produces the direct-image base-change map with explicit
formulas on sections.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

namespace Construction.OpenPullbackSquare

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- Direct images along the two equal composite scheme morphisms agree. -/
def pushforwardSquareIso :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pushforwardComp (f ∣_ U) U.ι).symm

/-- The base-change map as a mate across open-restriction adjunctions. -/
def openBaseChangeMap :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor U.ι ⟶
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward (f ∣_ U) :=
  ((mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
    (Scheme.Modules.restrictAdjunction U.ι)).symm
      (TwoSquare.mk _ _ _ _ (pushforwardSquareIso f U).hom)).natTrans

/-- The mate is computed using the unit on the inverse-image open and
the counit on the base open. -/
theorem openBaseChangeMap_app (M : X.Modules) :
    (openBaseChangeMap f U).app M =
      (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pushforward f).map
          ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M)) ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        ((pushforwardSquareIso f U).hom.app
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)) ≫
      (Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.pushforward (f ∣_ U)).obj
          ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)) := by
  dsimp [openBaseChangeMap, mateEquiv]
  simp only [Category.id_comp, Category.comp_id]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_id,
    (Scheme.Modules.restrictFunctor U.ι).map_id, Category.id_comp, Category.id_comp]

/-- Restriction does not change the underlying map on the image open. -/
theorem restrict_map_app {Z W : Scheme.{u}} (i : Z ⟶ W) [IsOpenImmersion i]
    {M N : W.Modules} (a : M ⟶ N) (V : Z.Opens) :
    ((Scheme.Modules.restrictFunctor i).map a).app V = a.app (i ''ᵁ V) := rfl

/-- Over the base open, the unit for its inverse-image open is an
isomorphism on direct images. -/
theorem restrictedUnit_isIso (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M))) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  rw [restrict_map_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  let V := f ⁻¹ᵁ U
  let O := f ⁻¹ᵁ (U.ι ''ᵁ W)
  have hle : O ≤ V := f.preimage_mono (U.ι_image_le W)
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ O) = O := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hle]
  have hi : IsIso (homOfLE (V.ι.image_preimage_le O)) := by
    rw [show homOfLE (V.ι.image_preimage_le O) = eqToHom he from Subsingleton.elim _ _]
    infer_instance
  exact Functor.map_isIso M.presheaf (homOfLE (V.ι.image_preimage_le O)).op

/-- The canonical open-base-change map is invertible. -/
theorem openBaseChangeMap_isIso : IsIso (openBaseChangeMap f U) := by
  have (M : X.Modules) : IsIso ((openBaseChangeMap f U).app M) := by
    rw [openBaseChangeMap_app]
    have := restrictedUnit_isIso f U M
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The left-adjoint square obtained from the isomorphism of composed
direct images. -/
def adjointPullbackSquare :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm
    (pushforwardSquareIso f U)

/-- The canonical restriction map is the mate of the invertible pullback square. -/
theorem rightMate :
    (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
      (TwoSquare.mk _ _ _ _ (adjointPullbackSquare f U).hom)).natTrans =
        openBaseChangeMap f U := by
  let γ := TwoSquare.mk _ _ _ _ (pushforwardSquareIso f U).hom
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι) γ
  apply congrArg TwoSquare.natTrans
  apply (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))).symm.injective
  rw [Equiv.symm_apply_apply]
  exact h.symm

private theorem pushforward_restrict_map (M : X.Modules)
    {V W : U.toScheme.Opens} (a : Opposite.op V ⟶ Opposite.op W) :
    ((Scheme.Modules.pushforward (f ∣_ U)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)).presheaf.map a =
      M.presheaf.map ((f ⁻¹ᵁ U).ι.opensFunctor.op.map
        ((TopologicalSpace.Opens.map (f ∣_ U).base).op.map a)) := rfl

private theorem map_three {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {W X Y Z : C} (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : W ⟶ Z)
    (h : a ≫ b ≫ c = d) : P.map a ≫ P.map b ≫ P.map c = P.map d := by
  rw [← P.map_comp, ← P.map_comp, h]

private theorem pushforwardSquareIso_app (M : (f ⁻¹ᵁ U).toScheme.Modules)
    (W : Y.Opens) :
    ((pushforwardSquareIso f U).hom.app M).app W =
      M.presheaf.map (eqToHom (show
        (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W) = (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W) by
          rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι,
            Scheme.Hom.comp_preimage])).op := by
  simp only [pushforwardSquareIso, Iso.trans_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  erw [Category.id_comp, Category.comp_id]

theorem map_app (M : X.Modules) (W : U.toScheme.Opens) :
    ((openBaseChangeMap f U).app M).app W =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W)).op := by
  rw [openBaseChangeMap_app]
  simp only [Scheme.Modules.Hom.comp_app, restrict_map_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app, pushforwardSquareIso_app,
    pushforward_restrict_map, Scheme.Modules.restrict_map]
  exact map_three M.presheaf _ _ _ _ (Subsingleton.elim _ _)

theorem unit_square (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (openBaseChangeMap f U).app ((Scheme.Modules.pullback f).obj M) =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        ((adjointPullbackSquare f U).hom.app M) := by
  have h := unit_mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
    (TwoSquare.mk _ _ _ _ (adjointPullbackSquare f U).hom) M
  change _ ≫
    ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
      (TwoSquare.mk _ _ _ _ (adjointPullbackSquare f U).hom)).natTrans).app _ = _ at h
  rw [rightMate] at h
  exact h

end Construction.OpenPullbackSquare

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenPullbackIs
