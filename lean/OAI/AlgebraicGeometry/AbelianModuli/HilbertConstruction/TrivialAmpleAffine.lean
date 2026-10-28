import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.Powers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Trivial Ample Affine -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TrivialAmpleAffine

noncomputable section

/-! A nonempty scheme with a field of global functions and an ample trivial bundle is affine. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

theorem trivialAmple_isAffine_of_globalFunctions_isField [Nonempty X]
    (hΓ : IsField Γ(X, ⊤)) (hL : (Line.Bundles.LineBundle.trivial X).IsAmple) : IsAffine X := by
  let : Field Γ(X, ⊤) := hΓ.toField
  let x : X := Classical.choice inferInstance
  obtain ⟨n, _, P, hP, s, hx, hs⟩ := hL.2 x
  obtain ⟨e⟩ := hP.unique (LineBundle.Powers.structureModule_isTensorPower X n)
  let t : End (Line.Bundles.structureModule X) := s ≫ e.hom
  have hD : Ample.LineBundles.sectionNonvanishing t = Ample.LineBundles.sectionNonvanishing s := Ample.Powers.sectionNonvanishing_comp_iso s e
  have ht : t ≠ 0 := by
    intro h
    have hz : Ample.LineBundles.sectionNonvanishing t = ⊥ := h ▸ ZeroSections.sectionNonvanishing_zero_of_frame (Iso.refl _)
    exact (show x ∈ (⊥ : X.Opens) from (hD.symm.trans hz) ▸ hx).elim
  have hv : Frame.Coordinates.structureModuleEndValue X t ≠ 0 := by
    intro h
    exact ht (Global.Sections.structureModuleEndValue_injective X (h.trans (map_zero (Frame.Coordinates.structureModuleEndValue X)).symm))
  let : IsIso t := (Global.Sections.structureModuleEnd_isIso_iff t).mpr (isUnit_iff_ne_zero.mpr hv)
  have htop : Ample.LineBundles.sectionNonvanishing s = ⊤ := hD.symm.trans (Ample.LineBundles.sectionNonvanishing_of_isIso t)
  have hA : IsAffineOpen (⊤ : X.Opens) := htop ▸ hs
  let : IsAffine (⊤ : X.Opens).toScheme := hA
  exact IsAffine.of_isIso X.topIso.inv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TrivialAmpleAffine
