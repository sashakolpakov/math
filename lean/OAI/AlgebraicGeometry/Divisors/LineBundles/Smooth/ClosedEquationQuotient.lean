import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth
import Mathlib.RingTheory.Smooth.Basic

/-! # Closed Equation Quotient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.ClosedEquationQuotient.BundleCycles

noncomputable section

/-! The quotient by the actual principal kernel of a smooth closed subscheme is a smooth algebra on every affine ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothClosedEquation_quotient {Y X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth Y.hom]
    (i : Y ⟶ X) [IsClosedImmersion i.left] (U : X.left.Opens) (hU : IsAffineOpen U)
    (s : Γ(X.left, U)) (hs : RingHom.ker (i.left.app U).hom = Ideal.span {s}) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
    Algebra.Smooth ℂ (Γ(X.left, U) ⧸ Ideal.span {s}) := by
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra X.hom U
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra (i.left ≫ X.hom) (i.left ⁻¹ᵁ U)
  let : Smooth (i.left ≫ X.hom) := i.w.symm ▸ inferInstanceAs (Smooth Y.hom)
  let : Algebra.Smooth ℂ Γ(Y.left, i.left ⁻¹ᵁ U) :=
    Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth (i.left ≫ X.hom) (i.left ⁻¹ᵁ U) (hU.preimage i.left)
  let a := Foundations.Scheme.ClosedImmersionDimension.sectionPullbackAlgHom i.left X.hom U
  let e := Ideal.quotientKerAlgEquivOfSurjective (Foundations.Scheme.ClosedImmersionDimension.sectionPullbackAlgHom_surjective i.left X.hom U hU)
  have h : Algebra.Smooth ℂ (Γ(X.left, U) ⧸ RingHom.ker a) :=
    Algebra.Smooth.of_equiv e.symm
  change Algebra.Smooth ℂ (Γ(X.left, U) ⧸ RingHom.ker (i.left.app U).hom) at h
  rw [hs] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.ClosedEquationQuotient.BundleCycles
