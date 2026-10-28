import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BundleIsoSheaf

/-! # Iso Identity Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An isomorphism of line bundles after the identity base change is an actual isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.nonempty_iso_of_pullback_isIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f]
    (L M : Line.Bundles.LineBundle X) (h : Nonempty ((L.pullback f).sheaf ≅ (M.pullback f).sheaf)) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  have h' : Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf L) =
      Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.classOf M) := Quotient.sound h
  exact Quotient.exact ((Line.Bundles.LineBundle.pullbackIso (asIso f)).injective h')

theorem IsoIdentityBaseChange.relativeBundleIso_identity_nonempty_iff {X S : Scheme.{u}} (p : X ⟶ S)
    (L M : Line.Bundles.LineBundle X) :
    Nonempty ((Relative.BundleIsoSheaf.relativeBundleIsoPresheaf p L M).obj (.op (Over.mk (𝟙 S)))) ↔
      Nonempty (L.sheaf ≅ M.sheaf) := by
  constructor
  · intro h
    exact Line.Bundles.LineBundle.nonempty_iso_of_pullback_isIso (Limits.pullback.snd (𝟙 S) p) L M h
  · rintro ⟨e⟩
    exact ⟨(Scheme.Modules.pullback (Limits.pullback.snd (𝟙 S) p)).mapIso e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
