import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFractionCoordinates

/-! # Model Principal Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelPrincipalFraction

noncomputable section

/-! The original local fraction in an arbitrary single degree is
carried to the literal native fraction input by the checked degree map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens) (g : ℕ) [SmoothOfRelativeDimension g X.hom]
  (a : Fin g → Γ(X.left,U.val))

abbrev opens := Principal.DeRhamSectionUnit.opens (Truncated.Witt.Ring p k n) X U
abbrev family := Supported.Comparison.family p k n X U g a

abbrev localIso (c : ℕ) := Principal.MappedSingleCoordinates.localCoordinates
  (TopCover.coefficients p k n X) (TopCover.form p k n X g)
  c g (opens p k n X U) (family p k n X U g a)

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem diagonal : localIso p k n X U g a g =
    PrincipalTopHomology.originalIso p k n X U g a g := rfl

def input (c : ℕ) (r : WittVector p k) :=
  (localIso p k n X U g a c).inv
    (AdditiveTopFractionCoordinates.ordinaryClass p k n X Y f hp U g a r)

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem coordinates (c : ℕ) (r : WittVector p k) :
    (localIso p k n X U g a c).hom (input p k n X Y f hp U g a c r) =
      AdditiveTopFractionCoordinates.ordinaryClass p k n X Y f hp U g a r := by
  exact Iso.inv_hom_id_apply _ _

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem degree_input (c : ℕ) (r : WittVector p k) :
    (PrincipalTopDegree.localChange p k n X g c
      (opens p k n X U) (family p k n X U g a)).hom
        (input p k n X Y f hp U g a c r) =
      AdditiveTopFraction.input p k n X Y f hp U g a r := by
  rw [AdditiveTopFractionCoordinates.input_eq]
  change (localIso p k n X U g a g).inv
      ((localIso p k n X U g a c).hom ((localIso p k n X U g a c).inv _)) = _
  rw [Iso.inv_hom_id_apply]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ModelPrincipalFraction
