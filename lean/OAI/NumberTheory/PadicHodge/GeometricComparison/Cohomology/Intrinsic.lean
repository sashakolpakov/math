import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.CrystallineComparison
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarFormsChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.IsoCohomology

/-! # Intrinsic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Cohomology's comparison transported through the actual generic-fiber and coefficient equivalences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Cohomology.Intrinsic.PadicBase

variable (q : ℕ) [Fact q.Prime]

theorem localScalarMap_eq : algebraMap ℤ_[q] ℚ_[q] =
    (DVR.PadicBase.localFieldEquiv q).toRingHom.comp (algebraMap ℤ_[q] (DVR.PadicBase.dvr q).K) :=
  RingHom.ext (fun x => (DVR.PadicBase.localFieldEquiv_algebraMap q x).symm)

def genericFiberRestrictionIso (X : Over (Spec (CommRingCat.of ℤ_[q]))) :
    ScalarFormsChange.SectionScalarChange.restrictBase (DVR.PadicBase.localFieldEquiv q).toRingHom
        ((Over.pullback (Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).obj X) ≅
      (DVR.PadicBase.dvr q).genericFiber X :=
  ScalarFormsChange.SectionScalarChange.restrictedFiberIso (DVR.PadicBase.localFieldEquiv q)
    (algebraMap ℤ_[q] (DVR.PadicBase.dvr q).K) (algebraMap ℤ_[q] ℚ_[q]) (localScalarMap_eq q) X

theorem totalCoefficientEquiv_eq :
    (DVR.PadicBase.unramifiedFieldEquiv q).trans (DVR.PadicBase.localFieldEquiv q) = GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q := by
  apply RingEquiv.toRingHom_injective
  exact (congrArg (fun f => (DVR.PadicBase.localFieldEquiv q).toRingHom.comp f)
    (DVR.PadicBase.coefficientInclusion_eq q).symm).trans (DVR.PadicBase.coefficientField_square q)

end Cohomology.Intrinsic.PadicBase

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.fractionDeRhamEquiv :
    AlgebraicGeometry.Crystalline.Cohomology.Foundations.algebraicDeRham (DVR.PadicBase.dvr q) A.integral.scheme 1
      ≃ₛₗ[(DVR.PadicBase.localFieldEquiv q).toRingHom] A.DeRham :=
  (GeometricComparison.DeRham.IsoCohomology.isoPullback (Cohomology.Intrinsic.PadicBase.genericFiberRestrictionIso q A.integral.scheme).hom 1).trans
    (GeometricComparison.DeRham.ScalarChange.SectionScalarChange.cohomologyEquiv (DVR.PadicBase.localFieldEquiv q) A.localFiber.scheme 1).symm

def Geometry.AbelianH1Model.smallToDeRhamEquiv (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    A.SmallCrystalline ≃ₛₗ[(GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q).toRingHom] A.DeRham := by
  letI : RingHomCompTriple (DVR.PadicBase.unramifiedFieldEquiv q).toRingHom
      (DVR.PadicBase.localFieldEquiv q).toRingHom
      ((DVR.PadicBase.unramifiedFieldEquiv q).trans (DVR.PadicBase.localFieldEquiv q)).toRingHom := ⟨rfl⟩
  letI : RingHomCompTriple (DVR.PadicBase.localFieldEquiv q).symm.toRingHom
      (DVR.PadicBase.unramifiedFieldEquiv q).symm.toRingHom
      ((DVR.PadicBase.unramifiedFieldEquiv q).trans (DVR.PadicBase.localFieldEquiv q)).symm.toRingHom := ⟨rfl⟩
  let e : A.SmallCrystalline ≃ₛₗ[
      ((DVR.PadicBase.unramifiedFieldEquiv q).trans (DVR.PadicBase.localFieldEquiv q)).toRingHom] A.DeRham :=
    (A.fractionComparison hCohomology).trans A.fractionDeRhamEquiv
  exact
    { __ := e.toAddEquiv
      map_smul' r x := (e.map_smulₛₗ r x).trans
        (congrArg (fun a => a • e x)
          (congrArg (fun σ => σ r) (Cohomology.Intrinsic.PadicBase.totalCoefficientEquiv_eq q))) }

def Geometry.AbelianH1Model.crystallineDeRhamEquiv (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham :=
  A.smallCrystallineEquiv.symm.trans (A.smallToDeRhamEquiv hCohomology)

theorem Geometry.AbelianH1Model.deRham_finite_of_Cohomology (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    FiniteDimensional ℚ_[q] A.DeRham := by
  let := A.crystalline_finite_of_Cohomology hCohomology
  exact (A.crystallineDeRhamEquiv hCohomology).finiteDimensional

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
