import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.Intrinsic
import OAI.NumberTheory.PadicHodge.GeometricComparison.EquivalentFiberNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.DeRhamAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-! # Fraction Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Cohomology's fraction-field de Rham realization is naturally identified with GeometricComparison's actual local realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.fractionDeRhamEquiv_naturality (f : A.ExtendingEndomorphism)
    (x : AlgebraicGeometry.Crystalline.Cohomology.Foundations.algebraicDeRham (DVR.PadicBase.dvr q) A.integral.scheme 1) :
    A.fractionDeRhamEquiv
        (AlgebraicGeometry.Crystalline.Cohomology.GoodReductionOperators.deRhamPullback (DVR.PadicBase.dvr q) f.integral.toMul.hom.hom 1 x) =
      A.deRhamPullback f (A.fractionDeRhamEquiv x) :=
  EquivalentFiberNaturality.SectionScalarChange.fiberCohomologyEquiv_naturality (DVR.PadicBase.localFieldEquiv q)
    (algebraMap ℤ_[q] (DVR.PadicBase.dvr q).K) (algebraMap ℤ_[q] ℚ_[q])
    (Cohomology.Intrinsic.PadicBase.localScalarMap_eq q) f.integral.toMul.hom.hom 1 x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
