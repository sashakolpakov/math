import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalTopHomology

/-! # Additive Top Fraction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFractionCoordinates

noncomputable section

/-! The additive residue input is the original single-degree class,
expressed through its canonical coefficient and unshifted coordinates. -/
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

def ordinaryClass (r : WittVector p k) :=
  (PrincipalTopHomology.coefficientIso p k n X U g a g).hom
    (PrincipalTopFraction.ordinaryClass p k n X Y f hp U g a r)

def singleClass (r : WittVector p k) :=
  (PrincipalTopHomology.originalIso p k n X U g a g).inv
    (ordinaryClass p k n X Y f hp U g a r)

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem input_coordinates (r : WittVector p k) :
    (PrincipalTopHomology.originalIso p k n X U g a g).hom
      (AdditiveTopFraction.input p k n X Y f hp U g a r) =
    ordinaryClass p k n X Y f hp U g a r := by
  have h := ConcreteCategory.congr_hom
    (PrincipalTopHomology.input_coordinates p k n X U g a g)
    (PrincipalTopFraction.singleClass p k n X Y f hp U g a r)
  change (PrincipalTopHomology.originalIso p k n X U g a g).hom
      (AdditiveTopFraction.input p k n X Y f hp U g a r) =
    (PrincipalTopHomology.coefficientIso p k n X U g a g).hom
      ((PrincipalTopHomology.nativeIso p k n X U g a g).hom
        ((PrincipalTopHomology.nativeIso p k n X U g a g).inv
          (PrincipalTopFraction.ordinaryClass p k n X Y f hp U g a r))) at h
  rw [Iso.inv_hom_id_apply] at h
  exact h

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] [SmoothOfRelativeDimension g X.hom] in
theorem input_eq (r : WittVector p k) :
    AdditiveTopFraction.input p k n X Y f hp U g a r =
      singleClass p k n X Y f hp U g a r := by
  apply (ConcreteCategory.bijective_of_isIso
    (PrincipalTopHomology.originalIso p k n X U g a g).hom).injective
  rw [input_coordinates, singleClass, Iso.inv_hom_id_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFractionCoordinates
