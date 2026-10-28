import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoordinatesOnOpenSubschemes

/-! # From Section Value -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.FromSectionValue

noncomputable section

/-! Recover a frame coordinate from the corresponding ordinary section-value equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {M : Y.Modules}

/-- A value equation determines a section's coordinate in a global frame. -/
theorem frameCoordinate_eq_of_value {P : X.Modules}
    (e t : Line.Bundles.structureModule X ⟶ P) [IsIso e] (c : Γ(X, ⊤))
    (h : t.app ⊤ (1 : Γ(X, ⊤)) = c • e.app ⊤ (1 : Γ(X, ⊤))) :
    Frame.Coordinates.frameCoordinate e t = c := by
  have hc := congrArg (fun z : Γ(P, ⊤) => (inv e).app ⊤ z) h
  have he : (inv e).app ⊤ (e.app ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) :=
    congrArg (fun a : Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X => a.app ⊤ (1 : Γ(X, ⊤)))
      (IsIso.hom_inv_id e)
  exact hc.trans (((inv e).app_smul c (e.app ⊤ (1 : Γ(X, ⊤)))).trans
    ((congrArg (fun z : Γ(X, ⊤) => c • z) he).trans (mul_one c)))

/-- A local value equation determines the coordinate after pullback to an open immersion. -/
theorem local_frameCoordinate_eq_of_value (f : X ⟶ Y) [IsOpenImmersion f]
    (s t : Line.Bundles.structureModule Y ⟶ M) [hs : IsIso (Ample.LineBundles.pullbackSection f s)] (c : Γ(X, ⊤))
    (h : t.app (f ''ᵁ ⊤) (1 : Γ(Y, f ''ᵁ ⊤)) =
      (f.appIso ⊤).inv c • s.app (f ''ᵁ ⊤) (1 : Γ(Y, f ''ᵁ ⊤))) :
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection f s) (Ample.LineBundles.pullbackSection f t) = c := by
  have : IsIso (Section.SectionRestriction.restrictSection f s) := (Local.CoordinateValues.restrictSection_isIso_iff f s).mpr hs
  have hv : (Section.SectionRestriction.restrictSection f t).app ⊤ (1 : Γ(X, ⊤)) =
      c • (Section.SectionRestriction.restrictSection f s).app ⊤ (1 : Γ(X, ⊤)) := by
    change (Section.SectionRestriction.restrictSection f t).app ⊤ (1 : Γ(X, ⊤)) =
      (f.appIso ⊤).inv c • (show Γ(M, f ''ᵁ ⊤) from
        (Section.SectionRestriction.restrictSection f s).app ⊤ (1 : Γ(X, ⊤)))
    exact (Section.SectionRestriction.restrictSection_app_one f t ⊤).trans (h.trans
      (congrArg (fun z : Γ(M, f ''ᵁ ⊤) => (f.appIso ⊤).inv c • z)
        (Section.SectionRestriction.restrictSection_app_one f s ⊤).symm))
  exact (Local.CoordinateValues.frameCoordinate_restrictSection f s t).trans
    (frameCoordinate_eq_of_value (Section.SectionRestriction.restrictSection f s) (Section.SectionRestriction.restrictSection f t) c hv)

/-- The local coordinate criterion stated directly on an open of the original scheme. -/
theorem local_frameCoordinate_eq_of_value_on_open (U : Y.Opens)
    (s t : Line.Bundles.structureModule Y ⟶ M) [IsIso (Ample.LineBundles.pullbackSection U.ι s)]
    (c : Γ(U.toScheme, ⊤))
    (h : t.app U (1 : Γ(Y, U)) = U.topIso.hom c • s.app U (1 : Γ(Y, U))) :
    Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι s) (Ample.LineBundles.pullbackSection U.ι t) = c := by
  let j : U.ι ''ᵁ ⊤ ⟶ U := eqToHom U.ι_image_top
  have hmap := congrArg (fun z : Γ(M, U) => M.presheaf.map j.op z) h
  have ht := (M.unitHomEquiv t).property j.op
  have hs := (M.unitHomEquiv s).property j.op
  have hc : Y.presheaf.map j.op (U.topIso.hom c) = (U.ι.appIso ⊤).inv c := by
    rw [U.ι_appIso]
    exact ConcreteCategory.congr_hom
      (Y.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom_inv_id c
  apply local_frameCoordinate_eq_of_value U.ι s t c
  exact ht.symm.trans (hmap.trans ((M.map_smul j (U.topIso.hom c)
    (s.app U (1 : Γ(Y, U)))).trans
      (congrArg₂ (fun a : Γ(Y, U.ι ''ᵁ ⊤) => fun z : Γ(M, U.ι ''ᵁ ⊤) => a • z) hc hs)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.FromSectionValue
