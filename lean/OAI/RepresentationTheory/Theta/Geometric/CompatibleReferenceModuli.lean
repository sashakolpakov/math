import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedBall
import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.ModuliPoint

/-! # Compatible Reference Moduli -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! A single reference fiber forces every fiber of the same compatible
neighborhood to be an actual original reference moduli point. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

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

include hz₀ in
theorem Data.ActiveHeckeThetaData.ReferencePELPointData.compatible_reference_moduli_point (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (z : H.compatible.neighborhood) :
    ∃ b : D.domain, Intrinsic.FamilyFrames.familyChartParameter C z ≫ f = D.referenceModuliMap hg b := by
  obtain ⟨b, hb⟩ := R.transportedReferenceKernel_ball f H z₀ hz₀ hs hdegree z
  exact ⟨b, R.referenceFiber_moduli_point f H z₀ hz₀ (D.referencePELPointData hg b) z hs hdegree hb⟩

end

end OAI.RepresentationTheory.Theta.Geometric
