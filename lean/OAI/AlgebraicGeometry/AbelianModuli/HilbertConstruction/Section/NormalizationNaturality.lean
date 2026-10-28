import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.NormalizedLineBundle

/-! # Normalization Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Normalization commutes with any square preserving the structural
morphism and section, including arbitrary Cartesian base change. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X Y S T : Scheme.{u}}
variable (p : X ⟶ S) (z : S ⟶ X) (q : Y ⟶ T) (t : T ⟶ Y)
variable (f : Y ⟶ X) (b : T ⟶ S)
variable (hp : f ≫ p = q ≫ b) (hz : t ≫ f = b ≫ z)

include hp hz in
theorem Line.Bundles.LineBundle.sectionNormalizeClass_natural (v : Line.Bundles.LineBundle.IsoClass X) :
    Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.sectionNormalizeClass p z v) =
      Line.Bundles.LineBundle.sectionNormalizeClass q t (Line.Bundles.LineBundle.pullbackClass f v) := by
  have h : Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.pullbackClass p (Line.Bundles.LineBundle.pullbackClass z v)) =
      Line.Bundles.LineBundle.pullbackClass q (Line.Bundles.LineBundle.pullbackClass t (Line.Bundles.LineBundle.pullbackClass f v)) := by
    rw [← Line.Bundles.LineBundle.pullbackClass_comp f p, hp, Line.Bundles.LineBundle.pullbackClass_comp q b,
      ← Line.Bundles.LineBundle.pullbackClass_comp b z, ← hz, Line.Bundles.LineBundle.pullbackClass_comp t f]
  change (Line.Bundles.LineBundle.pullbackClassMonoidHom f) (v / Line.Bundles.LineBundle.pullbackClass p (Line.Bundles.LineBundle.pullbackClass z v)) = _
  rw [map_div]
  change Line.Bundles.LineBundle.pullbackClass f v / Line.Bundles.LineBundle.pullbackClass f (Line.Bundles.LineBundle.pullbackClass p (Line.Bundles.LineBundle.pullbackClass z v)) = _
  rw [h]
  rfl

def Line.Bundles.LineBundle.sectionNormalized_pullbackIso (L : Line.Bundles.LineBundle X) :
    ((Line.Bundles.LineBundle.sectionNormalized p z L).pullback f).sheaf ≅
      (Line.Bundles.LineBundle.sectionNormalized q t (L.pullback f)).sheaf :=
  Classical.choice (Quotient.exact
    ((congrArg (Line.Bundles.LineBundle.pullbackClass f) (Line.Bundles.LineBundle.classOf_sectionNormalized p z L)).trans
      ((Line.Bundles.LineBundle.sectionNormalizeClass_natural p z q t f b hp hz (Line.Bundles.LineBundle.classOf L)).trans
        (Line.Bundles.LineBundle.classOf_sectionNormalized q t (L.pullback f)).symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
