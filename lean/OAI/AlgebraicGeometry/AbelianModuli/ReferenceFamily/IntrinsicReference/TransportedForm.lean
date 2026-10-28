import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestPolarization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestLattice
import OAI.RepresentationTheory.Theta.Geometric.Relative.IntegralPolarization

/-! # Transported Form -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The transported native reference marking retains the precise trace
polarization and identifies the full original integral lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (a : P.domain)
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action F)
    (z₀ : H.compatible.neighborhood)
    (hz₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.referencePoint hM κ hP hκ a)

theorem Models.FinePELModel.transportedNativeReferenceFieldMarking_polarization
    (z : H.compatible.neighborhood) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (M.complexTestFamily κ f).polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
      (M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z v)
      (M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z w) = P.traceForm v w := by
  rw [M.transportedNativeReferenceFieldMarking_apply, M.transportedNativeReferenceFieldMarking_apply]
  exact (H.compatible.rationalBetween_polarization (M.complexTestFamily κ f).polarized
    (M.complexTestFamily κ f).action z₀ z
    (M.nativeReferenceTestRationalMarking hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v)
    (M.nativeReferenceTestRationalMarking hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ w)).trans
      (M.nativeReferenceTestRationalMarking_polarization hM κ hP hκ f a
        (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v w)

theorem Models.FinePELModel.transportedNativeReferenceFieldMarking_integral
    (z : H.compatible.neighborhood) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z v ∈
      Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized
        (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety ↔ v ∈ P.lattice := by
  rw [M.transportedNativeReferenceFieldMarking_apply]
  exact (H.compatible.rationalBetween_integral (M.complexTestFamily κ f).polarized
    (M.complexTestFamily κ f).action z₀ z
    (M.nativeReferenceTestRationalMarking hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v)).trans
      (M.nativeReferenceTestRationalMarking_integral hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
