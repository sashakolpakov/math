import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestLevelExponential
import OAI.RepresentationTheory.Theta.Geometric.Relative.RationalExponential

/-! # Transported Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedLevel.FinePELModel

noncomputable section

/-! Every transported ordered level point is the exact exponential of
the corresponding divided original lattice vector. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.Relative.RationalExponential

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.nativeReferenceTestFiberIso

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

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

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models.FinePELModel.transportedNativeReferenceFieldMarking_level (z : H.compatible.neighborhood) (v : P.lattice) :
    RepresentationTheory.Theta.Geometric.Intrinsic.LevelTransport.presentedFullLevelPoint (M.complexTestFamily κ f).polarized.level (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z))
      (Multiplicative.ofAdd (P.fixedLevelLabel hP N v)) =
        HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized
          (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety.toOver)
          ((N : ℝ)⁻¹ • (M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z v.val).val) := by
  let A := M.complexTestFamily κ f
  let c := Multiplicative.ofAdd (P.fixedLevelLabel hP N v)
  have he := H.compatible.fiberBetween_level A.polarized A.action z₀ z c
  rw [M.nativeReferenceTestRationalMarking_level hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v,
    H.compatible.fiberBetween_rational_exp] at he
  exact he.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedLevel.FinePELModel
