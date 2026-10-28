import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.MorphismCoordinate
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalCoordinate
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Divisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorInverse

/-! # Morphism Rational Coordinate -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.MorphismRationalCoordinate.Cycles

noncomputable section

/-! The inverse rational section of a nonzero line-bundle map to
the structure sheaf has the negative divisor of its actual local equations. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
    (φ : L.sheaf ⟶ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)

def lineBundleMorphismFieldCoordinate (x : X) : X.functionField :=
  X.germToFunctionField (L.trivializingOpen x)
    (MorphismCoordinate.Cycles.lineBundleMorphismCoordinate L φ x (L.trivializingOpen x) le_rfl)

theorem lineBundleMorphismFieldCoordinate_on_open (x : X) (W : X.Opens) [Nonempty W]
    (hW : W ≤ L.trivializingOpen x) :
    lineBundleMorphismFieldCoordinate L φ x =
      X.germToFunctionField W (MorphismCoordinate.Cycles.lineBundleMorphismCoordinate L φ x W hW) := by
  rw [← MorphismCoordinate.Cycles.lineBundleMorphismCoordinate_restrict L φ x hW le_rfl]
  exact (RationalBoundary.BundleCycles.RationalUnitRepresentative.germ_restrict hW _).symm

theorem lineBundleMorphismFieldCoordinate_identity (x : X) :
    lineBundleMorphismFieldCoordinate L φ x * (L.rationalSectionCoordinate x).val =
      lineBundleMorphismFieldCoordinate L φ (genericPoint X) := by
  let W := L.rationalCoordinateDomain x
  rw [lineBundleMorphismFieldCoordinate_on_open L φ x W inf_le_left,
    L.rationalSectionCoordinate_on_open x W le_rfl,
    lineBundleMorphismFieldCoordinate_on_open L φ (genericPoint X) W inf_le_right]
  change X.germToFunctionField W _ * X.germToFunctionField W _ = X.germToFunctionField W _
  rw [← map_mul]
  exact congrArg (X.germToFunctionField W) (MorphismCoordinate.Cycles.lineBundleMorphismCoordinate_transition L φ x (genericPoint X)
    W inf_le_left inf_le_right)

variable (hφ : lineBundleMorphismFieldCoordinate L φ (genericPoint X) ≠ 0)

include hφ in
theorem lineBundleMorphismFieldCoordinate_ne_zero (x : X) :
    lineBundleMorphismFieldCoordinate L φ x ≠ 0 := by
  intro hx
  have h := lineBundleMorphismFieldCoordinate_identity L φ x
  rw [hx, zero_mul] at h
  exact hφ h.symm

def lineBundleMorphismInverseCoefficient : X.functionFieldˣ :=
  (Units.mk0 (lineBundleMorphismFieldCoordinate L φ (genericPoint X)) hφ)⁻¹

theorem lineBundleMorphismInverseCoefficient_coordinate (x : X) :
    (lineBundleMorphismInverseCoefficient L φ hφ).val * (L.rationalSectionCoordinate x).val =
      (lineBundleMorphismFieldCoordinate L φ x)⁻¹ := by
  apply mul_left_cancel₀ (lineBundleMorphismFieldCoordinate_ne_zero L φ hφ x)
  calc
    lineBundleMorphismFieldCoordinate L φ x *
        ((lineBundleMorphismInverseCoefficient L φ hφ).val * (L.rationalSectionCoordinate x).val) =
      (lineBundleMorphismInverseCoefficient L φ hφ).val *
        (lineBundleMorphismFieldCoordinate L φ x * (L.rationalSectionCoordinate x).val) := by ring
    _ = 1 := by
      rw [lineBundleMorphismFieldCoordinate_identity]
      exact inv_mul_cancel₀ hφ
    _ = lineBundleMorphismFieldCoordinate L φ x * (lineBundleMorphismFieldCoordinate L φ x)⁻¹ :=
      (mul_inv_cancel₀ (lineBundleMorphismFieldCoordinate_ne_zero L φ hφ x)).symm

theorem lineBundleMorphismInverseCoefficient_divisor [AlgebraicGeometry.IsNoetherian X] (x : X) :
    L.rationalSectionPointDivisorWithCoefficient (lineBundleMorphismInverseCoefficient L φ hφ) x =
      -X.ord (lineBundleMorphismFieldCoordinate L φ x) x := by
  rw [L.rationalSectionPointDivisorWithCoefficient_apply,
    lineBundleMorphismInverseCoefficient_coordinate, Principal.DivisorInverse.BundleCycles.PrincipalDivisorInverse.ord_inv]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.MorphismRationalCoordinate.Cycles
