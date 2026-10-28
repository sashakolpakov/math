import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeExact

/-! # QC Presentation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.QCPresentation

noncomputable section

/-!
# The global-section presentation of an affine quasi-coherent sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]

/-- The actual quasi-coherent sheaf is recovered from its global sections. -/
def presentation : (tilde.functor R).obj ((moduleSpecΓFunctor (R := R)).obj M) ≅ M := by
  let a := Scheme.Modules.fromTildeΓ (R := R) M
  have ha : IsIso a := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  exact @asIso _ _ _ _ a ha

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.QCPresentation
