import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units

/-! # Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames

noncomputable section

/-! Actual section frames on nonvanishing opens and regular ratios of sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L : X.Modules}

/-- A section is a global frame exactly when its nonvanishing open is the whole scheme. -/
theorem isIso_iff_sectionNonvanishing_eq_top (s : Line.Bundles.structureModule X ⟶ L) :
    IsIso s ↔ Ample.LineBundles.sectionNonvanishing s = ⊤ := by
  constructor
  · intro hs
    let := hs
    exact Ample.LineBundles.sectionNonvanishing_of_isIso s
  · intro hs
    apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally s
    intro x
    have hx : x ∈ Ample.LineBundles.sectionNonvanishing s := hs.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hxU⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    change X.Opens at U
    exact ⟨U, hxU, (Nonvanishing.isIso_pullbackSection_iff U.ι s).mp hU⟩

/-- A section really is invertible on its entire nonvanishing open. -/
instance pullbackSection_nonvanishing_isIso (s : Line.Bundles.structureModule X ⟶ L) :
    IsIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι s) := by
  apply (isIso_iff_sectionNonvanishing_eq_top _).mpr
  rw [Nonvanishing.sectionNonvanishing_pullback]
  ext x
  change (Ample.LineBundles.sectionNonvanishing s).ι x ∈ Ample.LineBundles.sectionNonvanishing s ↔ True
  exact iff_true_intro x.property

/-- The canonical frame supplied by a section on its nonvanishing open. -/
def sectionFrameIso (s : Line.Bundles.structureModule X ⟶ L) :
    Line.Bundles.structureModule (Ample.LineBundles.sectionNonvanishing s).toScheme ≅
      (Scheme.Modules.pullback (Ample.LineBundles.sectionNonvanishing s).ι).obj L :=
  asIso (Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι s)

/-- On the nonvanishing open of s, divide another section by the frame s. -/
def sectionRatioEnd (s t : Line.Bundles.structureModule X ⟶ L) :
    End (Line.Bundles.structureModule (Ample.LineBundles.sectionNonvanishing s).toScheme) :=
  Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t ≫ (sectionFrameIso s).inv

/-- The quotient of two sections is a regular function where the denominator is nonvanishing. -/
def sectionRatio (s t : Line.Bundles.structureModule X ⟶ L) : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤) :=
  (sectionRatioEnd s t).app ⊤ (1 : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤))

/-- The quotient recovers the numerator when multiplied by the denominator frame. -/
theorem sectionRatioEnd_frame (s t : Line.Bundles.structureModule X ⟶ L) :
    sectionRatioEnd s t ≫ (sectionFrameIso s).hom =
      Ample.LineBundles.pullbackSection (Ample.LineBundles.sectionNonvanishing s).ι t := by
  simp only [sectionRatioEnd, Category.assoc, Iso.inv_hom_id, Category.comp_id]

@[simp]
theorem sectionRatioEnd_self (s : Line.Bundles.structureModule X ⟶ L) : sectionRatioEnd s s = 𝟙 _ :=
  (sectionFrameIso s).hom_inv_id

@[simp]
theorem sectionRatio_self (s : Line.Bundles.structureModule X ⟶ L) : sectionRatio s s = 1 := by
  change (sectionRatioEnd s s).app ⊤ (1 : Γ((Ample.LineBundles.sectionNonvanishing s).toScheme, ⊤)) = _
  rw [sectionRatioEnd_self]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
