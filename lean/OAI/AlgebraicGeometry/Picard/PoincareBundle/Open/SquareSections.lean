import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareBaseChange

/-! # Square Sections -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareSections

noncomputable section

/-!
# The canonical open-square base-change map on actual sections
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry Opposite

universe u

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) [IsOpenImmersion iX] [IsOpenImmersion iY]
  (h : iX ≫ f = f' ≫ iY)

include h in
omit [IsOpenImmersion iX] in
/-- The open square identifies the inverse images of an open subset of the restricted base. -/
theorem preimage_image (W : Y'.Opens) :
    iX ⁻¹ᵁ (f ⁻¹ᵁ (iY ''ᵁ W)) = f' ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage, iY.preimage_image_eq]

include h in
/-- The section map is defined on the actual image open in the original covering scheme. -/
theorem image_preimage_le (W : Y'.Opens) :
    iX ''ᵁ (f' ⁻¹ᵁ W) ≤ f ⁻¹ᵁ (iY ''ᵁ W) := by
  rw [← preimage_image f f' iX iY h W]
  exact iX.image_preimage_le _

/-- Direct image of an open restriction acts on the corresponding original open morphism. -/
theorem pushforward_restrict_map (M : X.Modules) {V W : Y'.Opens} (a : op V ⟶ op W) :
    ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.restrictFunctor iX).obj M)).presheaf.map a =
      M.presheaf.map (iX.opensFunctor.op.map ((TopologicalSpace.Opens.map f'.base).op.map a)) := rfl

/-- The open counit on a restricted direct image is an original sheaf restriction map. -/
theorem counit_section (M : X.Modules) (W : Y'.Opens) :
    ((Scheme.Modules.restrictAdjunction iY).counit.app
      ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.restrictFunctor iX).obj M))).app W =
    M.presheaf.map (iX.opensFunctor.map ((TopologicalSpace.Opens.map f'.base).map
      (eqToHom (iY.preimage_image_eq W).symm))).op := rfl

/-- The canonical mate on sections is precisely the original sheaf restriction map. -/
theorem baseChangeMap_app_app (M : X.Modules) (W : Y'.Opens) :
    ((SquareBaseChange.baseChangeMap f f' iX iY h).app M).app W =
      M.presheaf.map (homOfLE (SquareSections.image_preimage_le f f' iX iY h W)).op := by
  rw [SquareBaseChange.baseChangeMap_app]
  simp only [Scheme.Modules.Hom.comp_app, counit_section]
  simp [SquareBaseChange.directImageSquare, Adjunction.restrict_map_app,
    Scheme.Modules.restrict_map]
  erw [Category.id_comp, Category.comp_id]
  erw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareSections
