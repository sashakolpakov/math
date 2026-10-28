import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinarySymbols
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormSections

/-! # Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Residue.Integral

noncomputable section

/-! The actual integral form section unit followed by the inverse native
PD comparison sends a fractional parameter form to its weighted residue. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (U : X.left.affineOpens)

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local instance truncated : Algebra S Γ(X.left, U.val) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X U.val
local instance witt : Algebra W Γ(X.left, U.val) :=
  Truncated.SmoothFrame.Complex.wittAlgebra p k n Γ(X.left, U.val)

variable (τ : Type) [LinearOrder τ]
  [Algebra (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [IsScalarTower (Truncated.Witt.Ring p k n)
    (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]
  [Algebra.Etale (MvPolynomial τ (Truncated.Witt.Ring p k n))
    (IntrinsicDeRham.SectionUnit.Intrinsic.ring (Truncated.Witt.Ring p k n) X U.val)]

def fromSections (g : ℕ) (x : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf S X g, U.val)) :=
  ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).inv.app (op U)).f g
    ((IntegralComparison.Etale.FormSections.Integral.unitIso S X U.val U.property τ g).symm x)

theorem fromSections_unit (g : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S Γ(X.left, U.val) g) :
    fromSections p k n X Y f hp U τ g (Integral.FormSectionUnit.unit S X g U.val ω) =
      ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).inv.app (op U)).f g ω := by
  change ((OrdinaryBaseIso.Ordinary.pdIso p k n X Y f hp).inv.app (op U)).f g
    ((IntegralComparison.Etale.FormSections.Integral.unitIso S X U.val U.property τ g).symm
      ((IntegralComparison.Etale.FormSections.Integral.unitIso S X U.val U.property τ g) ω)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem fromSections_fraction (g : ℕ) (v : Fin g → Γ(X.left, U.val)ˣ) (r : WittVector p k) :
    fromSections p k n X Y f hp U τ g
      (Integral.FormSectionUnit.unit S X g U.val
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S Γ(X.left, U.val)
          (algebraMap W Γ(X.left, U.val) r * (↑((∏ i, v i)⁻¹) : Γ(X.left, U.val)))
          (fun i => (v i : Γ(X.left, U.val))))) =
      r • PD.LogarithmicWedges.Forms.logarithmicWedge W Γ(X.left, U.val)
        (OrdinarySymbols.Ordinary.frame p k n X Y f hp U).ideal
        (OrdinarySymbols.Ordinary.frame p k n X Y f hp U).dividedPowers g v :=
  (fromSections_unit p k n X Y f hp U τ g _).trans
    (OrdinarySymbols.Ordinary.inverse_fraction p k n X Y f hp U g v r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.Residue.Integral
