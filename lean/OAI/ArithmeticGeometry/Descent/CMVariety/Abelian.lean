import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianFamily
import OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedFiberPresentations
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothArithmetic
import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianParameter

/-! # Abelian -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.Abelian

noncomputable section

/-! Unconditional number-field descent of a complex CM abelian variety.
The arithmetic group family, its smooth parameter, the fixed CM tuple,
local group rigidity, and the arithmetic specialization are constructed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem cm_abelian_variety_has_number_field_model (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (hCM : A.HasCMH1) :
    AbelianFiber.HasNumberFieldModel A := by
  let E := AlgebraicEnhancement.Abelian.CMEnhancement.ofHasCM A hCM
  obtain ⟨D⟩ := ConnectedEmbeddedCoefficients.Abelian.abelian_variety_has_geometric_group_coefficient_model A
  let U := D.abelian
  let s := D.data.toModel.coefficients
  let R₀ := Models.CoefficientSystem.Constructions.Foundations.coefficientRing ℚ ℂ s
  let q₀ := Spec.map (CommRingCat.ofHom (algebraMap ℚ R₀))
  let p := Models.CoefficientSystem.Constructions.Foundations.genericBaseMap ℚ ℂ s
  have : Algebra.FiniteType ℚ R₀ := Models.CoefficientSystem.Constructions.Foundations.coefficientRing_finiteType ℚ ℂ s
  have : LocallyOfFiniteType q₀ := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr (inferInstanceAs (Algebra.FiniteType ℚ R₀)))
  obtain ⟨C⟩ := SmoothArithmetic.Abelian.complex_point_has_smooth_arithmetic_chart q₀ p
  let R := C.ring
  let : Algebra R ℂ := C.point.toRingHom.toAlgebra
  have hR : Function.Injective (algebraMap R ℂ) := C.injective
  let V := U.pullback C.map
  let pR := Spec.map (CommRingCat.ofHom (algebraMap R ℂ))
  have hpR : pR ≫ C.map = p := C.recovers
  let c := AbelianCoefficientComparison.iteratedAbelianPullbackIso U C.map pR p hpR
  have : IsMonHom c.hom := AbelianCoefficientComparison.iteratedAbelianPullbackIso_group U C.map pR p hpR
  let e := c ≪≫ D.fiberIso
  have he : IsMonHom e.hom := inferInstanceAs (IsMonHom (c.hom ≫ D.fiberIso.hom))
  let P : StandardModuli.Abelian.ComplexAbelianPresentation (V.pullback pR) := {
    variety := A
    comparison := e
    comparison_group := he }
  let presentU : ∀ x : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (CommRingCat.of R₀), StandardModuli.Abelian.ComplexAbelianPresentation (U.pullback x) :=
    fun x => @EmbeddedFiberPresentations.Abelian.embeddedAbelianFiberPresentation R₀ _ D.relativeDimension U
      A.variety.presentation.ambientDimension D.data.embedding D.data.closedImmersion x
  let presentV := SmoothAbelianFiber.pullbackComplexFiberPresentations U C.map presentU
  obtain ⟨parameter⟩ := SmoothAbelianFiber.smooth_abelian_parameter_exists R hR V presentV (E.onPresentedFiber P)
  exact parameter.cm_fiber_has_numberField_model P E

end

end OAI.ArithmeticGeometry.Descent.CMVariety.Abelian
