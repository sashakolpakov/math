import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedFieldMarking
import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.LevelExponential
import OAI.RepresentationTheory.Theta.Geometric.Relative.RationalExponential

/-! # Transported Level -/

namespace OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedLevel

noncomputable section

/-! The transported reference marking gives the exact exponentials
of every original ordered full-level label throughout its neighborhood. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

namespace ActiveHeckeThetaData.ReferencePELPointData

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (Universal.PELConditions.complexUniversalPolarized D.pel hg f).abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
      (Universal.PELConditions.complexUniversalAction D.pel hg f) F)
    (z₀ : H.compatible.neighborhood) (hz₀ : Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = R.point)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.transportedFieldMarking_level (z : H.compatible.neighborhood) (v : D.pel.reference.lattice) :
    Intrinsic.LevelTransport.presentedFullLevelPoint (Universal.PELConditions.complexUniversalPolarized D.pel hg f).level (Intrinsic.FamilyFrames.familyChartParameter C z)
      (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z))
      (Multiplicative.ofAdd (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v)) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
          (Intrinsic.FamilyFrames.familyChartParameter C z)).variety.toOver)
          ((D.pel.level : ℝ)⁻¹ • (R.transportedFieldMarking f H z₀ hz₀ z v.val).val) := by
  let A := Universal.PELConditions.complexUniversalPolarized D.pel hg f
  let ρ := Universal.PELConditions.complexUniversalAction D.pel hg f
  let c := Multiplicative.ofAdd (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v)
  have he := H.compatible.fiberBetween_level A ρ z₀ z c
  rw [R.nativeUniversalRationalMarking_level f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ v,
    H.compatible.fiberBetween_rational_exp] at he
  exact he.symm

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedLevel
