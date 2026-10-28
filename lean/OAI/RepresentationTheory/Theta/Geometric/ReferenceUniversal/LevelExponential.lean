import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.UniversalLevel
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.RationalExponential

/-! # Level Exponential -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.LevelExponential

noncomputable section

/-! Every actual universal full-level label is the exponential of
its precisely divided original reference marking vector. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

namespace ActiveHeckeThetaData.ReferencePELPointData

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.universalFiberIso Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hx : x ≫ f = R.point)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking_level (v : D.pel.reference.lattice) :
    Intrinsic.LevelTransport.presentedFullLevelPoint (Universal.PELConditions.complexUniversalPolarized D.pel hg f).level x
      (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x)
      (Multiplicative.ofAdd (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v)) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.expMap (C := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) x).variety.toOver)
          ((D.pel.level : ℝ)⁻¹ • (R.nativeUniversalRationalMarking f x hx v.val).val) := by
  let : NeZero D.pel.level := ⟨by have h := hg.fullLevel; omega⟩
  let M := R.model.toNativeReferenceModel R.analytic
  let e := R.nativeUniversalFiberIso f x hx
  let : IsMonHom e.hom := R.nativeUniversalFiberIso_group f x hx
  have he := R.nativeUniversalFiberIso_level f x hx
    (Multiplicative.ofAdd (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v))
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom
    (((M.fixedFullLevel D.pel.level).hom.app (.op (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))))
      (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase
        (Multiplicative.ofAdd (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v)))).val = _ at he
  rw [M.fixedFullLevel_native_reference] at he
  exact he.symm.trans (Intrinsic.RationalExponential.nativeMap_rational_exp e.hom (D.pel.level : ℝ)⁻¹ (M.nativeReferenceMarking v.val))

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.LevelExponential
