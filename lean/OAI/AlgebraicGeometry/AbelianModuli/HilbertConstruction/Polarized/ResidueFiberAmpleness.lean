import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FieldProjectivity

/-! # Residue Fiber Ampleness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ResidueFiberAmpleness.PolarizedAbelianWithLevel

noncomputable section

/-! The canonical graph bundle of a polarized abelian family is ample
on every residue-field fiber of the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem graphBundle_isAmple_residueFiber
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (x : S) :
    (A.graphBundle.pullback (A.abelian.scheme.hom.fiberι x)).IsAmple :=
  (A.pullback (S.fromSpecResidueField x)).graphBundle_isAmple_overField.of_iso
    (A.graphBundle_baseChangeIso (S.fromSpecResidueField x))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ResidueFiberAmpleness.PolarizedAbelianWithLevel
