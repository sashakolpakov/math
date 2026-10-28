import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.FiberLevel
import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.Action
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PolarizedComparisonLevel
import OAI.RepresentationTheory.Theta.Geometric.DistinctFiberPELComparison

/-! # Moduli Point -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.ModuliPoint

noncomputable section

section

/-! The nearby reference comparison is an isomorphism of the literal
original PEL fibers, including their represented duals and full levels. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

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

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberLevelIso :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
      ((Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point).pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
      ((Universal.PELConditions.complexUniversalPolarized D.pel hg f).pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) :=
  (R.referenceFiberNativeComparison f H z₀ hz₀ R' z hs hdegree hk).toLevelIso
    (R.referenceFiberPolarizedIso_level f H z₀ hz₀ R' z hs hdegree hk)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberLevelIso_action (c : NumberField.RingOfIntegers E) :
    ((Universal.PELConditions.complexUniversalAction D.pel hg R'.point).pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).map c ≫
      (R.referenceFiberLevelIso f H z₀ hz₀ R' z hs hdegree hk).abelian.hom =
      (R.referenceFiberLevelIso f H z₀ hz₀ R' z hs hdegree hk).abelian.hom ≫
        ((Universal.PELConditions.complexUniversalAction D.pel hg f).pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).map c :=
  R.referenceFiberPolarizedIso_action f H z₀ hz₀ R' z hs hdegree hk c

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberPELIso :
    AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso
      ((Complex.PELClassification.complexUniversalFamily D.pel R'.point).pullback (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
      ((Complex.PELClassification.complexUniversalFamily D.pel f).pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) :=
  DistinctFiberPELComparison.pelFiberIsoOfPolarizedBetween (Complex.PELClassification.complexUniversalFamily D.pel R'.point) (Complex.PELClassification.complexUniversalFamily D.pel f)
    (Universal.PELConditions.complexUniversal_isPELFamily D.pel hg R'.point).1 (Universal.PELConditions.complexUniversal_isPELFamily D.pel hg f).1
    (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (Intrinsic.FamilyFrames.familyChartParameter C z).left
    (R.referenceFiberLevelIso f H z₀ hz₀ R' z hs hdegree hk)
    (R.referenceFiberLevelIso_action f H z₀ hz₀ R' z hs hdegree hk)

end ActiveHeckeThetaData.ReferencePELPointData

end

/-! The original reduced-test classification identifies the nearby
universal fiber with the actual reference moduli point of its period. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

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

include hs hdegree hk in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiber_moduli_point : Intrinsic.FamilyFrames.familyChartParameter C z ≫ f = R'.point := by
  apply R'.point_unique
  exact ⟨(Universal.ModuliFaithfulness.complexUniversalFiber_modelIso D.pel f (Intrinsic.FamilyFrames.familyChartParameter C z)).trans
    (((R'.universalFiberIso R'.point (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _)).trans
      (R.referenceFiberPELIso f H z₀ hz₀ R' z hs hdegree hk)).symm)⟩

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.ModuliPoint
