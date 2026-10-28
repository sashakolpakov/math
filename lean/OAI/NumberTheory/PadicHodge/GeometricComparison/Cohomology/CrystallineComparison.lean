import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.Good
import OAI.NumberTheory.PadicHodge.GeometricComparison.EquivalentScalarExtension

/-! # Crystalline Comparison -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The geometric Cohomology comparison on the actual split model, before changing the de Rham coefficient field to Q_q. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Cohomology.CrystallineComparison.PadicBase

instance fractionFieldAlgebra (q : ℕ) [Fact q.Prime] : Algebra (DVR.PadicBase.dvr q).K₀ (DVR.PadicBase.dvr q).K :=
  AlgebraicGeometry.Crystalline.Cohomology.Foundations.MixedCharacteristicDVR.coefficientAlgebra (DVR.PadicBase.dvr q)

end Cohomology.CrystallineComparison.PadicBase

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.e62SmallEquiv : A.SmallCrystalline ≃ₗ[(DVR.PadicBase.dvr q).K₀]
    AlgebraicGeometry.Crystalline.Cohomology.Foundations.rationalCrystalline (DVR.PadicBase.dvr q) A.integral.scheme 1 :=
  (eqToIso (congrArg (fun X => AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology q (ZMod q) X 1)
    (DVR.PadicBase.specialFiber_eq q A.integral.scheme).symm)).toLinearEquiv

def Geometry.AbelianH1Model.e62Comparison (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    ((DVR.PadicBase.dvr q).K ⊗[(DVR.PadicBase.dvr q).K₀]
      AlgebraicGeometry.Crystalline.Cohomology.Foundations.rationalCrystalline (DVR.PadicBase.dvr q) A.integral.scheme 1) ≃ₗ[(DVR.PadicBase.dvr q).K]
        AlgebraicGeometry.Crystalline.Cohomology.Foundations.algebraicDeRham (DVR.PadicBase.dvr q) A.integral.scheme 1 :=
  (hCohomology q (DVR.PadicBase.dvr q) A.integral.scheme 1).choose

def Geometry.AbelianH1Model.fractionComparison (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    A.SmallCrystalline ≃ₛₗ[(DVR.PadicBase.unramifiedFieldEquiv q).toRingHom]
      AlgebraicGeometry.Crystalline.Cohomology.Foundations.algebraicDeRham (DVR.PadicBase.dvr q) A.integral.scheme 1 :=
  A.e62SmallEquiv.trans ((EquivalentScalarExtension.ScalarExtension.equiv (DVR.PadicBase.unramifiedFieldEquiv q)
    (DVR.PadicBase.coefficientInclusion_eq q) _).trans (A.e62Comparison hCohomology))

theorem Geometry.AbelianH1Model.fractionComparison_apply (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (x : A.SmallCrystalline) :
    A.fractionComparison hCohomology x = A.e62Comparison hCohomology (1 ⊗ₜ[(DVR.PadicBase.dvr q).K₀] A.e62SmallEquiv x) := rfl

theorem Geometry.AbelianH1Model.e62Comparison_naturality (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (f : A.ExtendingEndomorphism)
    (x : (DVR.PadicBase.dvr q).K ⊗[(DVR.PadicBase.dvr q).K₀]
      AlgebraicGeometry.Crystalline.Cohomology.Foundations.rationalCrystalline (DVR.PadicBase.dvr q) A.integral.scheme 1) :
    A.e62Comparison hCohomology
        ((AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.crystallinePullback (DVR.PadicBase.dvr q) f.integral.toMul.hom.hom 1).baseChange
          (DVR.PadicBase.dvr q).K x) =
      AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.deRhamPullback (DVR.PadicBase.dvr q) f.integral.toMul.hom.hom 1 (A.e62Comparison hCohomology x) :=
  ((hCohomology q (DVR.PadicBase.dvr q) A.integral.scheme 1).choose_spec.2.2.2.1 f.integral.toMul.hom.hom).1 x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
