import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup

/-! # Normalized Line Bundle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Normalize a line bundle along a section by removing its base fiber.
The resulting class is trivial on the section and is unchanged by tensoring
with a line bundle pulled back from the base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X S : Scheme.{u}} (p : X ⟶ S) (z : S ⟶ X)

def Line.Bundles.LineBundle.sectionNormalized (L : Line.Bundles.LineBundle X) : Line.Bundles.LineBundle X :=
  L.tensor ((L.pullback z).reciprocalFrameBundle.pullback p)

def Line.Bundles.LineBundle.sectionNormalizeClass (q : Line.Bundles.LineBundle.IsoClass X) : Line.Bundles.LineBundle.IsoClass X :=
  q / Line.Bundles.LineBundle.pullbackClass p (Line.Bundles.LineBundle.pullbackClass z q)

theorem Line.Bundles.LineBundle.classOf_sectionNormalized (L : Line.Bundles.LineBundle X) :
    Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.sectionNormalized p z L) = Line.Bundles.LineBundle.sectionNormalizeClass p z (Line.Bundles.LineBundle.classOf L) := by
  rw [Line.Bundles.LineBundle.sectionNormalized, Line.Bundles.LineBundle.classOf_tensor]
  change Line.Bundles.LineBundle.classOf L * (Line.Bundles.LineBundle.pullbackClassMonoidHom p) (Line.Bundles.LineBundle.classOf (L.pullback z).reciprocalFrameBundle) = _
  rw [Line.Bundles.LineBundle.classOf_reciprocalFrameBundle, map_inv]
  rfl

variable (hz : z ≫ p = 𝟙 S)

include hz in
theorem Line.Bundles.LineBundle.sectionNormalizeClass_section (q : Line.Bundles.LineBundle.IsoClass X) :
    Line.Bundles.LineBundle.pullbackClass z (Line.Bundles.LineBundle.sectionNormalizeClass p z q) = 1 := by
  let Hp := Line.Bundles.LineBundle.pullbackClassMonoidHom p
  let Hz := Line.Bundles.LineBundle.pullbackClassMonoidHom z
  have h : Hz (Hp (Hz q)) = Hz q := by
    change Line.Bundles.LineBundle.pullbackClass z (Line.Bundles.LineBundle.pullbackClass p (Line.Bundles.LineBundle.pullbackClass z q)) = _
    rw [← Line.Bundles.LineBundle.pullbackClass_comp, hz, Line.Bundles.LineBundle.pullbackClass_id]
    rfl
  change Hz (q / Hp (Hz q)) = 1
  rw [map_div, h]
  exact div_self' (Hz q)

include hz in
theorem Line.Bundles.LineBundle.sectionNormalizeClass_baseTensor (q : Line.Bundles.LineBundle.IsoClass X) (b : Line.Bundles.LineBundle.IsoClass S) :
    Line.Bundles.LineBundle.sectionNormalizeClass p z (q * Line.Bundles.LineBundle.pullbackClass p b) = Line.Bundles.LineBundle.sectionNormalizeClass p z q := by
  let Hp := Line.Bundles.LineBundle.pullbackClassMonoidHom p
  let Hz := Line.Bundles.LineBundle.pullbackClassMonoidHom z
  have h : Hz (Hp b) = b := by
    change Line.Bundles.LineBundle.pullbackClass z (Line.Bundles.LineBundle.pullbackClass p b) = b
    rw [← Line.Bundles.LineBundle.pullbackClass_comp, hz, Line.Bundles.LineBundle.pullbackClass_id]
  change (q * Hp b) / Hp (Hz (q * Hp b)) = q / Hp (Hz q)
  rw [Hz.map_mul, h, Hp.map_mul]
  exact mul_div_mul_right_eq_div q (Hp (Hz q)) (Hp b)

theorem Line.Bundles.LineBundle.sectionNormalizeClass_fixed (q : Line.Bundles.LineBundle.IsoClass X) (hq : Line.Bundles.LineBundle.pullbackClass z q = 1) :
    Line.Bundles.LineBundle.sectionNormalizeClass p z q = q := by
  change q / (Line.Bundles.LineBundle.pullbackClassMonoidHom p) (Line.Bundles.LineBundle.pullbackClass z q) = q
  rw [hq, map_one, div_one]

def Line.Bundles.LineBundle.sectionNormalized_sectionIso (L : Line.Bundles.LineBundle X) :
    ((Line.Bundles.LineBundle.sectionNormalized p z L).pullback z).sheaf ≅ Line.Bundles.structureModule S :=
  Classical.choice (Quotient.exact
    ((congrArg (Line.Bundles.LineBundle.pullbackClass z) (Line.Bundles.LineBundle.classOf_sectionNormalized p z L)).trans
      (Line.Bundles.LineBundle.sectionNormalizeClass_section p z hz (Line.Bundles.LineBundle.classOf L))))

def Line.Bundles.LineBundle.sectionNormalized_fixedIso (L : Line.Bundles.LineBundle X)
    (hL : Nonempty ((L.pullback z).sheaf ≅ Line.Bundles.structureModule S)) :
    (Line.Bundles.LineBundle.sectionNormalized p z L).sheaf ≅ L.sheaf :=
  Classical.choice (Quotient.exact ((Line.Bundles.LineBundle.classOf_sectionNormalized p z L).trans
    (Line.Bundles.LineBundle.sectionNormalizeClass_fixed p z (Line.Bundles.LineBundle.classOf L) (Quotient.sound hL))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
