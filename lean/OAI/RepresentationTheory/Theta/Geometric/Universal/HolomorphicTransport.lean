import OAI.RepresentationTheory.Theta.Geometric.Universal.PELConditions
import OAI.RepresentationTheory.Theta.Geometric.Universal.PeriodFrame
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.HolomorphicTransport

/-! # Holomorphic Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.HolomorphicTransport

noncomputable section

/-! Construct the full compatible holomorphic transport for the
original universal PEL family on every smooth integral complex test base. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.complexSpace) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

def complexUniversalHolomorphicTransport :
    Intrinsic.HolomorphicTransport.NativeHolomorphicTransport (PELConditions.complexUniversalPolarized D hg f) (PELConditions.complexUniversalAction D hg f)
      (PeriodFrame.complexUniversalPeriodFrame D hg f x) :=
  Classical.choice (Intrinsic.HolomorphicTransport.exists_nativeHolomorphicTransport (PELConditions.complexUniversalPolarized D hg f)
    (PELConditions.complexUniversalAction D hg f) (PeriodFrame.complexUniversalPeriodFrame D hg f x)
    (lt_of_lt_of_le (by decide : 0 < 3) hg.fullLevel))

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.HolomorphicTransport
