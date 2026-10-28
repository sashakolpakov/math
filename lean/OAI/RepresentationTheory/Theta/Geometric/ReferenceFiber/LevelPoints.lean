import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.IntrinsicRational
import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedLevel
import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.RationalMarking
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.RationalExponential

/-! # Level Points -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.LevelPoints

noncomputable section

/-! The algebraized nearby reference comparison preserves every
original ordered full-level point in the actual native presentations. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

local instance : IsReduced (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).left :=
  inferInstanceAs (IsReduced (Spec (.of ℂ)))

namespace ActiveHeckeThetaData.ReferencePELPointData

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
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

variable {b : D.domain} (R' : D.ReferencePELPointData hg b)
    (z : H.compatible.neighborhood)

variable (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hk : (H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
      (R.transportedReferenceLabel f H z₀ hz₀) z).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val})

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberComparison Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalRationalMarking Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberPolarizedIso

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberPolarizedIso_presented_level
    (c : Multiplicative (Fin (2 * (3 * s)) → ZMod D.pel.level)) :
    let P := PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
      (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
    let Q := PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z)
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P.comparison.inv ≫ (R.referenceFiberPolarizedIso f H z₀ hz₀ R' z hs hdegree hk).hom ≫
      Q.comparison.hom)
      (Intrinsic.LevelTransport.presentedFullLevelPoint (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point).level
        (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) P c) =
      Intrinsic.LevelTransport.presentedFullLevelPoint (Universal.PELConditions.complexUniversalPolarized D.pel hg f).level (Intrinsic.FamilyFrames.familyChartParameter C z) Q c := by
  let P := PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
    (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
  let Q := PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Intrinsic.FamilyFrames.familyChartParameter C z)
  let e := R.referenceFiberPolarizedIso f H z₀ hz₀ R' z hs hdegree hk
  let : IsMonHom e.hom := R.referenceFiberPolarizedIso_group f H z₀ hz₀ R' z hs hdegree hk
  let : IsMonHom P.comparison.hom := P.comparison_group
  let : IsMonHom Q.comparison.hom := Q.comparison_group
  let j := P.comparison.inv ≫ e.hom ≫ Q.comparison.hom
  let : IsMonHom j := inferInstance
  obtain ⟨v, hv⟩ := D.pel.reference.fixedLevelLabel_surjective hg.reference_admissible D.pel.level c.toAdd
  have hc : Multiplicative.ofAdd (D.pel.reference.fixedLevelLabel hg.reference_admissible D.pel.level v) = c :=
    congrArg Multiplicative.ofAdd hv
  dsimp only
  rw [← hc]
  refine Intrinsic.RationalExponential.nativeMap_point_of_rational_exp (A := P.variety) (B := Q.variety) j (D.pel.level : ℝ)⁻¹
    (R'.nativeUniversalRationalMarking R'.point (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v.val)
    (R.transportedFieldMarking f H z₀ hz₀ z v.val) _ _ ?_ ?_ ?_
  · exact R'.nativeUniversalRationalMarking_level R'.point
      (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v
  · exact R.transportedFieldMarking_level f H z₀ hz₀ z v
  · exact R.referenceFiberPolarizedIso_marking f H z₀ hz₀ R' z hs hdegree hk v.val

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.LevelPoints
