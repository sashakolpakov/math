import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TrivialAmpleAffine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability

/-! # Ample Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AmpleTriviality

noncomputable section

/-! A pointed proper reduced connected scheme over a field with an ample torsion line bundle is a point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsReduced X] [ConnectedSpace X]
variable (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)

include x hx in
theorem properPointed_trivialAmple_isIso (hL : (Line.Bundles.LineBundle.trivial X).IsAmple) : IsIso p := by
  let : IsAffine X := TrivialAmpleAffine.trivialAmple_isAffine_of_globalFunctions_isField
    (ConnectedReducedConstants.properConnectedReduced_globalSections_isField p) hL
  have h : p ≫ x = 𝟙 X := by
    simpa only [Category.comp_id] using (ConnectedReducedConstants.properConnectedReduced_map_eq_constant p (𝟙 X) x hx).symm
  exact ⟨⟨x, h, hx⟩⟩

include x hx in
theorem properPointed_ample_torsion_isIso (L : Line.Bundles.LineBundle X) (hL : L.IsAmple)
    (n : ℕ) (hn : 0 < n) (e : (L.tensorPower n).sheaf ≅ Line.Bundles.structureModule X) : IsIso p :=
  properPointed_trivialAmple_isIso p x hx ((hL.tensorPower n hn).of_iso e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AmpleTriviality
