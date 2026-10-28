import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates

noncomputable section

/-! Regular coordinates in a line-bundle frame and their change-of-frame identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L : X.Modules}

/-- A structure-module endomorphism determines its global scalar as a ring homomorphism. -/
def structureModuleEndValue (X : Scheme.{u}) : End (Line.Bundles.structureModule X) →+* Γ(X, ⊤) where
  toFun a := a.app ⊤ (1 : Γ(X, ⊤))
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' a b :=
    (TensorPower.Units.structureModuleEnd_app a ⊤ (show Γ(X, ⊤) from b.app ⊤ (1 : Γ(X, ⊤)))).trans
      (mul_comm (show Γ(X, ⊤) from b.app ⊤ (1 : Γ(X, ⊤)))
        (show Γ(X, ⊤) from a.app ⊤ (1 : Γ(X, ⊤))))

/-- The endomorphism obtained by writing a section in a global frame. -/
def frameCoordinateEnd (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] : End (Line.Bundles.structureModule X) :=
  t ≫ inv s

/-- The global regular function giving the coordinate of a section in a frame. -/
def frameCoordinate (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] : Γ(X, ⊤) :=
  structureModuleEndValue X (frameCoordinateEnd s t)

theorem frameCoordinateEnd_frame (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] :
    frameCoordinateEnd s t ≫ s = t := by
  simp only [frameCoordinateEnd, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

@[simp]
theorem frameCoordinate_self (s : Line.Bundles.structureModule X ⟶ L) [IsIso s] : frameCoordinate s s = 1 := by
  change structureModuleEndValue X (s ≫ inv s) = 1
  rw [IsIso.hom_inv_id]
  exact map_one (structureModuleEndValue X)

/-- The transition function between two frames is a unit. -/
theorem frameCoordinate_isUnit (s t : Line.Bundles.structureModule X ⟶ L) [IsIso s] [IsIso t] :
    IsUnit (frameCoordinate s t) := by
  have : IsIso (frameCoordinateEnd s t) := by dsimp [frameCoordinateEnd]; infer_instance
  exact ((isUnit_iff_isIso (frameCoordinateEnd s t)).mpr this).map (structureModuleEndValue X)

/-- Changing the frame multiplies every coordinate by the same transition function. -/
theorem frameCoordinate_change (s t r : Line.Bundles.structureModule X ⟶ L) [IsIso s] [IsIso t] :
    frameCoordinate s r = frameCoordinate s t * frameCoordinate t r := by
  have he : frameCoordinateEnd s r = frameCoordinateEnd s t * frameCoordinateEnd t r := by
    change r ≫ inv s = (r ≫ inv t) ≫ (t ≫ inv s)
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  exact (congrArg (structureModuleEndValue X) he).trans (map_mul (structureModuleEndValue X) _ _)

/-- The section-ratio construction is the regular coordinate in its canonical denominator frame. -/
theorem sectionRatio_eq_frameCoordinate (s t : Line.Bundles.structureModule X ⟶ L) :
    Section.Frames.sectionRatio s t = frameCoordinate
      (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι s)
      (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t) := by
  simp only [Section.Frames.sectionRatio, frameCoordinate, structureModuleEndValue,
    Section.Frames.sectionRatioEnd, frameCoordinateEnd, Section.Frames.sectionFrameIso, asIso_inv]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.Coordinates
