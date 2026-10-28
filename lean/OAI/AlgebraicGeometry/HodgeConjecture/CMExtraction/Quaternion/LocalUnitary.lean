import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointTopology
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.PointIntegral
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.UnitaryPresentation
import OAI.RepresentationTheory.Theta.Adelic.IntegralTopology
import OAI.NumberTheory.Quaternion.Arithmetic.LocalAdeles

/-! # Local Unitary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalUnitary

noncomputable section

/-! The quaternion map into the actual localized diagonal Hermitian form,
with integral subgroup control at each finite place. -/

open scoped Classical _root_.NumberField
open Filter OAI.NumberTheory.Quaternion.Arithmetic.LocalAdeles
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.IntegralTopology

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.UnitaryPresentation.Quadratic

theorem diagonalForm_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (b : R) : (UnitaryMatrixEquiv.Quadratic.diagonalForm b).map f = UnitaryMatrixEquiv.Quadratic.diagonalForm (f b) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 2 <;>
      simp [UnitaryMatrixEquiv.Quadratic.diagonalForm, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient, hi]
  · simp [UnitaryMatrixEquiv.Quadratic.diagonalForm, hij]

theorem unitaryFormCongr_continuous {R : Type*} [CommRing R] [StarRing R]
    [TopologicalSpace R] (H K : Matrix (Fin 3) (Fin 3) R) (h : H = K) :
    Continuous (CM.UnitaryPresentation.Quadratic.unitaryFormCongr H K h) :=
  continuous_subtype_val.subtype_mk _

variable (F : Type) [Field F] [NumberField F] (a b : F)

theorem localized_diagonalForm (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) v =
      UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)
        (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F a v) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v b)) := by
  rw [RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm, diagonalForm_map]
  apply congrArg UnitaryMatrixEquiv.Quadratic.diagonalForm
  apply QuadraticAlgebra.ext <;> simp [RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal, RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange]

def quaternionLocalUnitary (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v) →*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) (.inr v)) :=
  (CM.UnitaryPresentation.Quadratic.unitaryFormCongr _ _ (localized_diagonalForm F a b (.inr v)).symm).toMonoidHom.comp
    (PointOne.quaternionPointUnitary a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)))

theorem quaternionLocalUnitary_continuous
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    Continuous (quaternionLocalUnitary F a b v) :=
  (unitaryFormCongr_continuous _ _ (localized_diagonalForm F a b (.inr v)).symm).comp
    (PointTopology.quaternionPointUnitary_continuous a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)))

def quaternionLocalUnitaryContinuous
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v) →ₜ*
      RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) (.inr v)) :=
  ⟨quaternionLocalUnitary F a b v, quaternionLocalUnitary_continuous F a b v⟩

theorem quaternionLocalUnitary_integral
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hb : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) b ∈ RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)) :
    Set.MapsTo (quaternionLocalUnitary F a b v)
      (NumberTheory.Quaternion.Arithmetic.LocalAdeles.integralLocalSubgroup (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v))
      (RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) (.inr v)) := by
  intro g hg
  constructor
  · intro i j
    exact RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff F a (.inr v) _
      (PointIntegral.quaternionPointUnitary_integral a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)) _ hb g hg.1 i j).1
      (PointIntegral.quaternionPointUnitary_integral a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)) _ hb g hg.1 i j).2
  · intro i j
    exact RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff F a (.inr v) _
      (PointIntegral.quaternionPointUnitary_inverse_integral a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)) _ hb g hg.2 i j).1
      (PointIntegral.quaternionPointUnitary_inverse_integral a b (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v)) _ hb g hg.2 i j).2

theorem quaternionLocalUnitary_eventually_integral :
    ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) in cofinite,
      Set.MapsTo (quaternionLocalUnitary F a b v)
        (NumberTheory.Quaternion.Arithmetic.LocalAdeles.integralLocalSubgroup (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v))
        (RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) (.inr v)) := by
  filter_upwards [Sum.inr_injective.tendsto_cofinite.eventually (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F b)] with v hv
  exact quaternionLocalUnitary_integral F a b v hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalUnitary
