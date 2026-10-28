import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestFieldMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.IsoLabels
import OAI.RepresentationTheory.Theta.Geometric.Relative.FieldEquiv

/-! # Transported Marking -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Transport the constructed reference marking over the entire CM field
on the actual compatible native family neighborhood. A fixed rational
label represents this marking in the original central period frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.nativeReferenceTestFiberIso

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

def Models.FinePELModel.transportedNativeReferenceFieldMarking (z : H.compatible.neighborhood) :
    let A := M.complexTestFamily κ f
    let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E]
      Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A.polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety := by
  let A := M.complexTestFamily κ f
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀)
  let := RepresentationTheory.Theta.Geometric.CompatibleFieldEquiv.familyPeriodFieldModule A.polarized A.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
  exact (M.nativeReferenceTestFieldMarking hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀).trans
    (H.compatible.fieldBetween A.polarized A.action z₀ z)

theorem Models.FinePELModel.transportedNativeReferenceFieldMarking_apply
    (z : H.compatible.neighborhood) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z v =
      H.compatible.rationalBetween (M.complexTestFamily κ f).polarized
        (M.complexTestFamily κ f).action z₀ z
        (M.nativeReferenceTestRationalMarking hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v) := by
  unfold Models.FinePELModel.transportedNativeReferenceFieldMarking
  rw [LinearEquiv.trans_apply, RepresentationTheory.Theta.Geometric.Intrinsic.CompatibleTransport.NativeCompatibleTransport.fieldBetween_apply,
    M.nativeReferenceTestFieldMarking_apply]

def Models.FinePELModel.transportedNativeReferenceLabel :
    Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalReferenceLabel (E := E)
      (A := (M.complexTestFamily κ f).polarized) (C := C) := by
  let e := M.nativeReferenceTestFiberIso hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀
  have : IsMonHom e.hom :=
    M.nativeReferenceTestFiberIso_group hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀
  exact H.referenceIsoLabel (Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP) z₀ e

theorem Models.FinePELModel.transportedNativeReferenceLabel_value
    (z : H.compatible.neighborhood) (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    H.rationalTransport z (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀ v) =
      M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z v := by
  rw [M.transportedNativeReferenceFieldMarking_apply]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
