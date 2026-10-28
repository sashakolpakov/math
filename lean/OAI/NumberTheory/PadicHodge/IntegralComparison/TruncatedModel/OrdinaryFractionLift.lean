import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopFractionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryFractionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.TopCoefficientIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.TopClassLift

/-! # Ordinary Fraction Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryFractionLift.Ordinary

noncomputable section

/-! The original additive fractional class has the native coefficient
coordinate through the same two universe lifts and the actual Cech
homology comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (V : X.left.affineOpens) (g : ℕ) [SmoothOfRelativeDimension g X.hom]
  (a : Fin g → Γ(X.left,V.val))

abbrev diagram := PrincipalSource.OpenTopClass.target V.val V.property
  (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf (Truncated.Witt.Ring p k n) X g)

abbrev family := Supported.Comparison.family p k n X V g a

def liftIso (m : ℕ) := AugmentedCech.TopClassCoefficients.homologyIso
  (family p k n X V g a) AdditiveTop.Comparison.lift
  (diagram p k n X V g) m

omit [Fintype k] [CharP k p] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
private theorem native_top
    (x : (PrincipalTopSingle.coefficient p k n X V g).obj
      (op (AugmentedOrdered.CechCoordinates.topObject (family p k n X V g a) g (by simp)))) :
    (PrincipalTopHomology.coefficientIso p k n X V g a g).hom
      (AugmentedOrdered.CechTopClass.topClass (family p k n X V g a)
        (PrincipalTopSingle.coefficient p k n X V g) g (by simp) x) =
    AugmentedCech.TopClassMap.map (family p k n X V g a)
      (PrincipalTopSingle.coefficient p k n X V g ⋙
        AdditiveTop.Comparison.forget p k) g (by simp) x := by
  dsimp only [PrincipalTopHomology.coefficientIso]
  rw [AugmentedCech.TopCoefficientIso.eq]
  exact Augmented.TopClassLift.forget (family p k n X V g a)
    (PrincipalTopSingle.coefficient p k n X V g) g (by simp) x

omit [IsSeparated Y.hom] in
omit [IsProper X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem ordinaryClass (r : WittVector p k) :
    AdditiveTopFractionCoordinates.ordinaryClass p k n X Y f hp V g a r =
    (liftIso p k n X V g a g).hom
      (ULift.up.{2,1} (ULift.up.{1,0}
        (AugmentedCech.TopClassMap.map (family p k n X V g a) (diagram p k n X V g)
          g (by simp)
          (Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g
            (PrincipalFraction.topOpen p k n X Y f hp V g a).val
            (PrincipalFraction.fraction p k n X Y f hp V g a r))))) := by
  dsimp only [AdditiveTopFractionCoordinates.ordinaryClass,
    PrincipalTopFraction.ordinaryClass]
  rw [native_top]
  exact (Augmented.TopClassLift.lift (family p k n X V g a)
    (diagram p k n X V g) g (by simp)
    (Integral.FormSectionUnit.unit (Truncated.Witt.Ring p k n) X g
      (PrincipalFraction.topOpen p k n X Y f hp V g a).val
      (PrincipalFraction.fraction p k n X Y f hp V g a r))).symm

variable (Z : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  (π : X ⟶ Z) (U : Z.left.Opens) (hVU : V.val ≤ π.left ⁻¹ᵁ U)
  (t : Fin g → Γ(Z.left,U))

omit [IsSeparated Y.hom] in
omit [IsProper X.hom] [X.left.IsSeparated] [SmoothOfRelativeDimension g X.hom] in
theorem targetClass (r : WittVector p k) :
    AdditiveTopFractionCoordinates.ordinaryClass p k n X Y f hp V g
      (ResidueFraction.localParameters p k n X Z π U V hVU g t) r =
    (liftIso p k n X V g
      (ResidueFraction.localParameters p k n X Z π U V hVU g t) g).hom
      (ULift.up.{2,1} (ULift.up.{1,0}
        (OrdinaryFractionRestriction.Ordinary.targetClass p k n X Y f hp Z π U V hVU g t r))) :=
  ordinaryClass p k n X Y f hp V g
    (ResidueFraction.localParameters p k n X Z π U V hVU g t) r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.OrdinaryFractionLift.Ordinary
