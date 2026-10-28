import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.Adjunction

/-! # Square Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareBaseChange

noncomputable section

/-!
# Canonical module base change in an arbitrary square of open subschemes
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry

universe u

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
  (h : iX ≫ f = f' ≫ iY)

/-- The equality of composite scheme maps gives the actual direct-image square. -/
def directImageSquare :
    Scheme.Modules.pushforward iX ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward f' ⋙ Scheme.Modules.pushforward iY :=
  Scheme.Modules.pushforwardComp iX f ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
    (Scheme.Modules.pushforwardComp f' iY).symm

/-- The canonical base-change map is the mate across the two open-restriction adjunctions. -/
def baseChangeMap :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor iY ⟶
      Scheme.Modules.restrictFunctor iX ⋙ Scheme.Modules.pushforward f' :=
  ((mateEquiv (Scheme.Modules.restrictAdjunction iX) (Scheme.Modules.restrictAdjunction iY)).symm
    (TwoSquare.mk _ _ _ _ (directImageSquare f f' iX iY h).hom)).natTrans

/-- The open-square mate has an explicit unit, square, and counit formula. -/
theorem baseChangeMap_app (M : X.Modules) :
    (baseChangeMap f f' iX iY h).app M =
      (Scheme.Modules.restrictFunctor iY).map ((Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictAdjunction iX).unit.app M)) ≫
      (Scheme.Modules.restrictFunctor iY).map ((directImageSquare f f' iX iY h).hom.app
        ((Scheme.Modules.restrictFunctor iX).obj M)) ≫
      (Scheme.Modules.restrictAdjunction iY).counit.app
        ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.restrictFunctor iX).obj M)) := by
  dsimp [baseChangeMap, mateEquiv]
  simp only [Category.id_comp, Category.comp_id]
  erw [(Scheme.Modules.restrictFunctor iY).map_id,
    (Scheme.Modules.restrictFunctor iY).map_id, Category.id_comp]

/-- If the source open contains the inverse image of the target open, the restricted unit is invertible. -/
theorem restrictedUnit_isIso (hpre : f ⁻¹ᵁ iY.opensRange ≤ iX.opensRange) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor iY).map ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction iX).unit.app M))) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  rw [Adjunction.restrict_map_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  let O := f ⁻¹ᵁ (iY ''ᵁ W)
  have hle : O ≤ iX.opensRange := (f.preimage_mono (iY.image_le_opensRange W)).trans hpre
  have he : iX ''ᵁ (iX ⁻¹ᵁ O) = O :=
    (iX.image_preimage_eq_opensRange_inf O).trans (inf_eq_right.mpr hle)
  have hi : IsIso (homOfLE (iX.image_preimage_le O)) := by
    rw [show homOfLE (iX.image_preimage_le O) = eqToHom he from Subsingleton.elim _ _]
    infer_instance
  exact Functor.map_isIso M.presheaf (homOfLE (iX.image_preimage_le O)).op

/-- The canonical direct-image base-change map is invertible on a cartesian open square. -/
theorem baseChangeMap_isIso (hpre : f ⁻¹ᵁ iY.opensRange ≤ iX.opensRange) :
    IsIso (baseChangeMap f f' iX iY h) := by
  have (M : X.Modules) : IsIso ((baseChangeMap f f' iX iY h).app M) := by
    rw [baseChangeMap_app]
    have := restrictedUnit_isIso f iX iY hpre M
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The left square obtained from the actual direct-image square by conjugation. -/
def leftSquare :
    Scheme.Modules.restrictFunctor iY ⋙ Scheme.Modules.pullback f' ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor iX :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction iX))
    ((Scheme.Modules.restrictAdjunction iY).comp (Scheme.Modules.pullbackPushforwardAdjunction f'))).symm
    (directImageSquare f f' iX iY h)

/-- The right mate of this left square is exactly the actual open base-change map. -/
theorem rightMate_leftSquare :
    DescentRestriction.rightMate (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f') (leftSquare f f' iX iY h) =
        baseChangeMap f f' iX iY h := by
  let δ := TwoSquare.mk _ _ _ _ (directImageSquare f f' iX iY h).hom
  have he := iterated_mateEquiv_conjugateEquiv_symm
    (Scheme.Modules.pullbackPushforwardAdjunction f) (Scheme.Modules.pullbackPushforwardAdjunction f')
    (Scheme.Modules.restrictAdjunction iY) (Scheme.Modules.restrictAdjunction iX) δ
  apply congrArg TwoSquare.natTrans
  apply (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f')).symm.injective
  change (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f')).symm
    ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f'))
        (TwoSquare.mk _ _ _ _ (leftSquare f f' iX iY h).hom)) = _
  rw [Equiv.symm_apply_apply]
  exact he.symm

/-- A cartesian open square has invertible canonical right mate. -/
theorem rightMate_isIso (hpre : f ⁻¹ᵁ iY.opensRange ≤ iX.opensRange) :
    IsIso (DescentRestriction.rightMate (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f') (leftSquare f f' iX iY h)) := by
  rw [rightMate_leftSquare]
  exact baseChangeMap_isIso f f' iX iY h hpre

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareBaseChange
