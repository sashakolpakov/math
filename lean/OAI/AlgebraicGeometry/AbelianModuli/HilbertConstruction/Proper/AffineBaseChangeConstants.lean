import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.GlobalFunctionsPushout
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ConnectedReducedConstants

/-! # Affine Base Change Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AffineBaseChangeConstants

noncomputable section

/-! Global functions remain constant after affine base change of a pointed connected
reduced proper scheme over a field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y P : Scheme.{u}}

theorem properField_affineBaseChange_globalFunctions_isIso
    (p : X ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated p]
    [IsReduced X] [ConnectedSpace X] (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    {a : P ⟶ X} {b : P ⟶ Y} {g : Y ⟶ Spec (.of K)} (H : IsPullback a b p g)
    [IsAffine Y] : IsIso b.appTop := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  have hp : IsSeparated (p ≫ terminal.from (Spec (.of K))) := inferInstance
  have : IsSeparated (terminal.from X) := (terminal.comp_from p) ▸ hp
  have : IsIso p.appTop := (ConnectedReducedConstants.properConnectedReducedPointGlobalIso p x hx).isIso_hom
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  have : Module.Flat Γ(Spec (.of K), ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g) := inferInstance
  exact HilbertConstruction.Flat.GlobalFunctionsPushout.flatBaseChange_globalFunctions_isIso H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AffineBaseChangeConstants
