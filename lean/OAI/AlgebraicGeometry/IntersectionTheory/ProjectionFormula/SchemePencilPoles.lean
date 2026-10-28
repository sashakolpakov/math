import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DVRPencilPoles
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FunctionDivisor

/-! # Scheme Pencil Poles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SchemePencilPoles

noncomputable section

/-! The polar cycle of a rational pencil is unchanged by subtracting
a regular function, in particular any scalar parameter. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

theorem poles_sub (Z : Scheme) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (hNormal : ∀ x : Z, IsIntegrallyClosed (Z.presheaf.stalk x))
    (g a : Z.functionField) (hg : g ≠ 0) (hga : g - a ≠ 0)
    (ha : ∀ x : Z, Order.coheight x = 1 →
      ∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u = a) :
    PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z (g - a)⁻¹) = PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z g⁻¹) := by
  apply Finsupp.ext
  intro x
  rw [PositiveCycle.positivePart_apply, PositiveCycle.positivePart_apply, Affine.DivisorNorm.rationalPrincipalDivisor_apply, Affine.DivisorNorm.rationalPrincipalDivisor_apply,
    Principal.DivisorInverse.ord_inv, Principal.DivisorInverse.ord_inv, Int.cast_neg, Int.cast_neg]
  by_cases hx : Order.coheight x = 1
  · let := hNormal x
    let := PositiveOrder.stalk_isDVR x hx
    obtain ⟨u, hu⟩ := ha x hx
    have hgu : g - algebraMap (Z.presheaf.stalk x) Z.functionField u ≠ 0 := by rwa [hu]
    have h := DVRPencilPoles.negative_part_sub (Z.presheaf.stalk x) Z.functionField g hg u hgu
    rw [hu] at h
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
    change max (-((WithZero.log (Ring.ordFrac (Z.presheaf.stalk x) (g - a)) : ℤ) : ℚ)) 0 =
      max (-((WithZero.log (Ring.ordFrac (Z.presheaf.stalk x) g) : ℤ) : ℚ)) 0
    exact_mod_cast h
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx, Scheme.ord_eq_zero_of_coheight_neq_one hx]

theorem poles_sub_scalar (Z : Scheme) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (π : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (hNormal : ∀ x : Z, IsIntegrallyClosed (Z.presheaf.stalk x))
    (g : Z.functionField) (hg : g ≠ 0) (a : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra π
    g - algebraMap ℂ Z.functionField a ≠ 0 →
      PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z (g - algebraMap ℂ Z.functionField a)⁻¹) =
        PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z g⁻¹) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra π
  intro hga
  apply poles_sub Z hNormal g _ hg hga
  intro x _
  let := FunctionDivisor.stalkScalarAlgebra π x
  let := FunctionDivisor.stalkScalarTower π x
  exact ⟨algebraMap ℂ (Z.presheaf.stalk x) a,
    (IsScalarTower.algebraMap_apply ℂ (Z.presheaf.stalk x) Z.functionField a).symm⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SchemePencilPoles
