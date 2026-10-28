import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenTopClass
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.DifferentialSymbolRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResidueFraction

/-! # Ordinary Fraction Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryFractionRestriction.Ordinary

noncomputable section

/-! The original additive fractional top class restricts to the literal
ordinary fraction on the chosen source neighborhood. The coefficient
remains the same arbitrary Witt lift. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem coefficient (r : WittVector p k) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g).presheaf.map
      (homOfLE (PrincipalResidue.ResidueRestriction.topBelow π.left U V.val V.property hVU t)).op
      (Principal.DifferentialSymbolRestriction.sourceValue
        (Truncated.Witt.Ring p k n) X Z π U hU t (Truncated.Witt.quotient p k n r)) =
    Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g
      (ResidueFraction.topOpen p k n X Y f hp Z π U V hVU g t).val
      (PrincipalFraction.fraction p k n X Y f hp V g
        (ResidueFraction.localParameters p k n X Z π U V hVU g t) r) := by
  exact (Principal.DifferentialSymbolRestriction.restriction
    (Truncated.Witt.Ring p k n) X Z π U hU V.val V.property hVU t
      (Truncated.Witt.quotient p k n r)).trans
    (congrArg (Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g
      (ResidueFraction.topOpen p k n X Y f hp Z π U V hVU g t).val)
      (ResidueFraction.ordinarySymbol_eq p k n X Y f hp Z π U hU V hVU g t r))

abbrev sourceClass (r : WittVector p k) :=
  AugmentedCech.TopClassMap.map (PrincipalPoint.Fraction.family U t)
    (PrincipalSource.OpenTopClass.source π.left U hU
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)) g (by simp)
    (Principal.DifferentialSymbolRestriction.sourceValue
      (Truncated.Witt.Ring p k n) X Z π U hU t (Truncated.Witt.quotient p k n r))

abbrev targetClass (r : WittVector p k) :=
  AugmentedCech.TopClassMap.map
    (PrincipalPoint.Fraction.family V.val
      (ResidueFraction.localParameters p k n X Z π U V hVU g t))
    (PrincipalSource.OpenTopClass.target V.val V.property
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)) g (by simp)
    (Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g
      (ResidueFraction.topOpen p k n X Y f hp Z π U V hVU g t).val
      (PrincipalFraction.fraction p k n X Y f hp V g
        (ResidueFraction.localParameters p k n X Z π U V hVU g t) r))

omit [IsProper X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem topClass (r : WittVector p k) :
    homologyMap (PrincipalSource.OpenTopClass.complexMap π.left U hU V.val V.property hVU
      (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g) t) g
      (sourceClass p k n X Z π U hU g t r) =
    targetClass p k n X Y f hp Z π U V hVU g t r := by
  exact (PrincipalSource.OpenTopClass.apply π.left U hU V.val V.property hVU
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g) t
    (Principal.DifferentialSymbolRestriction.sourceValue
      (Truncated.Witt.Ring p k n) X Z π U hU t (Truncated.Witt.quotient p k n r))).trans
    (congrArg (AugmentedCech.TopClassMap.map
      (PrincipalPoint.Fraction.family V.val
        (ResidueFraction.localParameters p k n X Z π U V hVU g t))
      (PrincipalSource.OpenTopClass.target V.val V.property
        (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)) g (by simp))
      (coefficient p k n X Y f hp Z π U hU V hVU g t r))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryFractionRestriction.Ordinary
