import OAI.RepresentationTheory.Theta.Geometric.Universal.FamilyPeriodCharts
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrameActions
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.Matrices
import OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage

/-! # Period Frame -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.PeriodFrame

noncomputable section

/-! The full holomorphic frame and its family endomorphisms are
constructed for the original universal PEL family. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.complexSpace) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

def complexUniversalPeriodFrame : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame (FamilyPeriodCharts.complexUniversalFamilyCharts D f x) :=
  Classical.choice (Intrinsic.FamilyFrames.exists_nativeFamilyPeriodFrame (FamilyPeriodCharts.complexUniversalFamilyCharts D f x)
    (Complex.FamilyPresentation.complexUniversalFiberPresentation D hg f))

theorem complexUniversalPeriodFrame_center :
    Intrinsic.FamilyFrames.familyChartParameter (FamilyPeriodCharts.complexUniversalFamilyCharts D f x)
      (Intrinsic.FamilyFrames.familyChartCenter (FamilyPeriodCharts.complexUniversalFamilyCharts D f x)) = x :=
  Family.ChartOpenImage.familyChartParameter_center (FamilyPeriodCharts.complexUniversalFamilyCharts D f x)

omit [IsIntegral S.left] [Smooth S.hom] in
def complexUniversalEndomorphism (a : NumberField.RingOfIntegers E) :
    (Complex.PELClassification.complexUniversalFamily D f).abelian.scheme ⟶ (Complex.PELClassification.complexUniversalFamily D f).abelian.scheme :=
  AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap (Complex.PELClassification.complexUniversalFamily D f).abelian.scheme ((Complex.PELClassification.complexUniversalFamily D f).action a)

omit [IsIntegral S.left] [Smooth S.hom] in
instance complexUniversalEndomorphism_group (a : NumberField.RingOfIntegers E) :
    IsMonHom (complexUniversalEndomorphism D f a) :=
  AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_isMonHom (Complex.PELClassification.complexUniversalFamily D f).abelian.scheme ((Complex.PELClassification.complexUniversalFamily D f).action a)

omit [IsIntegral S.left] [Smooth S.hom] in
theorem complexUniversalEndomorphism_fiber (a : NumberField.RingOfIntegers E) :
    ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S (Complex.PELClassification.complexUniversalFamily D f).abelian (complexUniversalEndomorphism D f a) x =
      AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap ((Complex.PELClassification.complexUniversalFamily D f).pullback x.left).abelian.scheme
        (((Complex.PELClassification.complexUniversalFamily D f).pullback x.left).action a) :=
  ((Complex.PELClassification.complexUniversalFamily D f).pullback_action_schemeMap x.left a).symm

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.PeriodFrame
