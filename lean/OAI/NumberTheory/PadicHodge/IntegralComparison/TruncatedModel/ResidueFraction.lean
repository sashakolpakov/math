import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.ResidueRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FractionClass
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback

/-! # Residue Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueFraction

noncomputable section

/-! The restricted original scalar residue has exactly the numerator,
reciprocal product, and differential parameters of the native integral
fraction. A Witt lift carries the arbitrary original scalar unchanged. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped BigOperators
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.ResidueRestriction

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (Z : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  (π : X ⟶ Z) (U : Z.left.Opens) (hU : IsAffineOpen U)
  (V : X.left.affineOpens) (hVU : V.val ≤ π.left ⁻¹ᵁ U)
  (g : ℕ) (t : Fin g → Γ(Z.left,U))

local instance ambientAlgebra : Algebra (Truncated.Witt.Ring p k n) Γ(Z.left,U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) Z U
local instance sourceAlgebra (W : X.left.Opens) : Algebra (Truncated.Witt.Ring p k n) Γ(X.left,W) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (Truncated.Witt.Ring p k n) X W

abbrev localParameters := PrincipalResidue.ResidueRestriction.parameters π.left U V.val hVU t
abbrev topOpen := PrincipalFraction.topOpen p k n X Y f hp V g
  (localParameters p k n X Z π U V hVU g t)

abbrev coefficient (r : WittVector p k) :=
  PrincipalResidue.ResidueRestriction.coefficientMap π.left U V.val V.property hVU t
    (PrincipalResidue.SymbolCoordinates.coefficient U hU t (Truncated.Witt.Ring p k n)
      (Truncated.Witt.quotient p k n r))

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem coefficient_eq (r : WittVector p k) :
    coefficient p k n X Z π U hU V hVU g t r =
      algebraMap (Truncated.Witt.Ring p k n) Γ(X.left,(topOpen p k n X Y f hp Z π U V hVU g t).val)
          (Truncated.Witt.quotient p k n r) *
        (↑((∏ j, PrincipalFraction.coordinateUnit p k n X Y f hp V g
          (localParameters p k n X Z π U V hVU g t) j)⁻¹) :
          Γ(X.left,(topOpen p k n X Y f hp Z π U V hVU g t).val)) := by
  let units := PrincipalFraction.coordinateUnit p k n X Y f hp V g
    (localParameters p k n X Z π U V hVU g t)
  have hu (j : Fin g) : (units j : Γ(X.left,(topOpen p k n X Y f hp Z π U V hVU g t).val)) =
      X.left.presheaf.map (Principal.SectionPresheaf.inclusion V.val
        (PrincipalResidue.SymbolCoordinates.top V.val (localParameters p k n X Z π U V hVU g t))).op
        (localParameters p k n X Z π U V hVU g t j) :=
    PrincipalFraction.coordinateUnit_val p k n X Y f hp V g
      (localParameters p k n X Z π U V hVU g t) j
  have h := PrincipalResidue.ResidueRestriction.coefficient π.left U hU V.val V.property hVU t
    (Truncated.Witt.Ring p k n) units hu (Truncated.Witt.quotient p k n r)
  have hb := (AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback.DeRhamPullback.sectionPullbackLE π U V.val hVU).commutes
    (Truncated.Witt.quotient p k n r)
  have hr := (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras (Truncated.Witt.Ring p k n) X).map
    (Principal.SectionPresheaf.inclusion V.val (PrincipalResidue.SymbolCoordinates.top V.val
      (localParameters p k n X Z π U V hVU g t))).op).hom).commutes
      (Truncated.Witt.quotient p k n r)
  have hbase := (congrArg (fun a => X.left.presheaf.map
      (Principal.SectionPresheaf.inclusion V.val (PrincipalResidue.SymbolCoordinates.top V.val
        (localParameters p k n X Z π U V hVU g t))).op a) hb).trans hr
  exact h.trans (congrArg (fun a => a * (↑((∏ j, units j)⁻¹) :
    Γ(X.left,(topOpen p k n X Y f hp Z π U V hVU g t).val))) hbase)

abbrev ordinarySymbol (r : WittVector p k) :=
  AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol (Truncated.Witt.Ring p k n)
    Γ(X.left,(topOpen p k n X Y f hp Z π U V hVU g t).val)
    (coefficient p k n X Z π U hU V hVU g t r)
    (fun j => X.left.presheaf.map
      (Principal.SectionPresheaf.inclusion V.val (PrincipalResidue.SymbolCoordinates.top V.val
        (localParameters p k n X Z π U V hVU g t))).op
      (localParameters p k n X Z π U V hVU g t j))

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem ordinarySymbol_eq (r : WittVector p k) :
    ordinarySymbol p k n X Y f hp Z π U hU V hVU g t r =
      PrincipalFraction.fraction p k n X Y f hp V g
        (localParameters p k n X Z π U V hVU g t) r := by
  dsimp only [ordinarySymbol]
  rw [coefficient_eq p k n X Y f hp Z π U hU V hVU g t r]
  change AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol _ _ _ _ = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol _ _ _ _
  congr 1
  funext j
  exact (PrincipalFraction.coordinateUnit_val p k n X Y f hp V g
    (localParameters p k n X Z π U V hVU g t) j).symm

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem integralSymbol_eq (r : WittVector p k) :
    ULift.up.{2,1} (ULift.up.{1,0}
      ((Integral.IntrinsicFormNormalization.Intrinsic.iso (Truncated.Witt.Ring p k n) X
        (topOpen p k n X Y f hp Z π U V hVU g t).val g).hom
        (Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g
          (topOpen p k n X Y f hp Z π U V hVU g t).val
          (ordinarySymbol p k n X Y f hp Z π U hU V hVU g t r)))) =
      FractionClass.Integral.fraction p k n X Y f hp V g
        (localParameters p k n X Z π U V hVU g t) r := by
  rw [ordinarySymbol_eq]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueFraction
