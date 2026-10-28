import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCoordinatesM
import OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage

/-! # Parameter Holomorphic -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.ParameterHolomorphic

noncomputable section

/-! Family parameters are holomorphic in the original native scheme
manifold because their inverse affine charts evaluate regular functions analytically. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions

theorem affineParameter_holomorphic
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (A : CommAlgCat ℂ) [IsDomain A] [Algebra.Smooth ℂ A]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ S) [IsOpenImmersion i.left]
    {ι : Type} [Fintype ι] (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (ι → ℂ))
    (he : ∀ a : A, ContDiffOn ℂ ω (fun z => e.symm z a) e.target)
    {z : ι → ℂ} (hz : z ∈ e.target) :
    MDifferentiableAt (𝓘(ℂ, ι → ℂ))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
      (fun w => AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm w)) z := by
  obtain ⟨f, hf, hzf⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.exists_smoothDomain_affineRegularChart (e.symm z)
  obtain ⟨g, hg, hcoords⟩ := hf.2
  let t := e.symm.trans f
  have hzt : z ∈ t.source := ⟨hz, hzf⟩
  have ht := (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.contDiffOn_affineChartTransition e f he g hg hcoords).contDiffAt (t.open_source.mem_nhds hzt)
  have htd : MDifferentiableAt (𝓘(ℂ, ι → ℂ))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)) t z :=
    mdifferentiableAt_iff_differentiableAt.mpr (ht.differentiableAt (by simp))
  let c := AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme A i f
  have hc := (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.Constructions.ProjectiveCoordinates.mdifferentiable_affineChartOnScheme (X := S) A i f hf).mdifferentiableAt_symm
    (f.map_source hzf)
  apply (hc.comp z htd).congr_of_eventuallyEq
  filter_upwards [t.open_source.mem_nhds hzt] with w hw
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (e.symm w) = c.symm (f (e.symm w))
  rw [AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_symm_apply]
  have hwf : e.symm w ∈ f.source := hw.2
  exact congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) (f.left_inv hwf).symm

theorem familyChartParameter_holomorphic
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom] {g : ℕ}
    {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left} {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    (C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x) {z : Intrinsic.FamilyFrames.FamilyChartBase C}
    (hz : z ∈ C.charts.charts.neighborhood) :
    MDifferentiableAt (𝓘(ℂ, Intrinsic.FamilyFrames.FamilyChartBase C))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
      (Intrinsic.FamilyFrames.familyChartParameter C) z :=
  affineParameter_holomorphic C.algebra C.openMap C.charts.charts.charts.base
    C.charts.charts.charts.regularBase (C.charts.charts.withinBase hz)

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.ParameterHolomorphic
