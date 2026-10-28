import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Affine Open Smooth -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Smooth coordinate algebras of actual affine opens

The scalar algebra comes from the given structure morphism to `Spec K`.
Smoothness on every affine open is inherited from the native smooth scheme
morphism, transported through the canonical global-section isomorphism for
the spectrum of the scalar ring. Integrality gives a domain on every
nonempty open.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The scalar homomorphism on an affine open of a smooth scheme is smooth. -/
theorem Foundations.Scheme.AffineOpenSmooth.specSectionScalarMap_smooth {K : Type u} [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (U : X.Opens) (hU : IsAffineOpen U) :
    (Foundations.Scheme.SpecScalarTransport.specSectionScalarMap f U).Smooth := by
  exact (RingHom.Smooth.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (.of K)).inv (f.appLE ⊤ U le_top)).mpr
      (f.smooth_appLE (isAffineOpen_top (Spec (.of K))) hU le_top)

/-- The actual scalar algebra of an affine open in a smooth scheme is smooth. -/
theorem Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth {K : Type u} [CommRing K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
    Algebra.Smooth K Γ(X, U) :=
  Foundations.Scheme.AffineOpenSmooth.specSectionScalarMap_smooth f U hU

/-- An integral scheme's actual coordinate algebra on a nonempty open is a domain. -/
instance ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left]
    (U : X.left.Opens) [Nonempty U] : IsDomain (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) := by
  change IsDomain Γ(X.left, U)
  infer_instance

/-- The actual coordinate algebra on any affine open of a smooth complex
scheme is smooth over the complex numbers. -/
theorem ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    Algebra.Smooth ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) :=
  Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth X.hom U hU

end

end OAI.AlgebraicGeometry
