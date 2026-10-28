import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleChartTopDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SectionProjectiveModuleChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityChartIdeal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationNoetherian
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ClosedComplement

/-! # Top Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.TopDegree.BundleCycles

noncomputable section

/-! The actual glued infinity ideal has the expected top degree
for a constant-rank conormal compactification over an integral center. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

instance conormalCenter_isNoetherian {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y]
    (I : Y.IdealSheafData) : AlgebraicGeometry.IsNoetherian I.subscheme :=
  Open.ClosedComplement.BundleCycles.closedImmersion_isNoetherian I.subschemeι

instance conormalCenter_isSeparated {Y : Scheme.{0}} [Y.IsSeparated]
    (I : Y.IdealSheafData) : I.subscheme.IsSeparated := ⟨by
  rw [← CategoryTheory.Limits.terminal.comp_from I.subschemeι]
  infer_instance⟩

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)
    [IsIntegral s.ker.subscheme]
    [Smooth (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker)]
    [GeometricallyIntegral (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker)]
    (f : s.ker.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (n : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) n)

include p hs in
theorem globalConormalChow_top_degree (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d)
    (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (InfinityBundle.Cycles.globalConormalInfinityIdealLineBundle s.ker)
        (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker ≫ f) d n
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) f n hp d α)) =
      (-1 : ℚ) ^ n • α := by
  obtain ⟨U, hU, hfinite, hprojective⟩ := Global.SectionProjectiveModuleChart.BundleCycles.globalSection_exists_projectiveModuleChart p s hs
    (genericPoint s.ker.subscheme)
  let R := Γ(Y, U.1) ⧸ s.ker.ideal U
  let M := (s.ker.ideal U).Cotangent
  let : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  let : IsNoetherianRing R := inferInstance
  let : Module.Finite R M := hfinite
  let : Module.Projective R M := hprojective
  let i : Spec (.of R) ⟶ s.ker.subscheme := Support.Projection.BundleCycles.supportCoefficientChart s.ker U
  let j : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) ⟶ Conormal.ProjectiveGluing.BundleCycles.globalConormalProjective s.ker :=
    (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover s.ker).f U
  have hi : IsOpenImmersion i := Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion s.ker U
  have hj : IsOpenImmersion j := Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveCover_isOpenImmersion s.ker U
  let : Nonempty (Spec (.of R)) := ⟨Classical.choose hU⟩
  let : IsIntegral (Spec (.of R)) := isIntegral_of_isOpenImmersion i
  let : IsDomain R := (affine_isIntegral_iff (.of R)).mp inferInstance
  exact LineBundles.Projective.ModuleChartTopDegree.BundleCycles.projectiveModuleChart_top_degree (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) f
    (InfinityBundle.Cycles.globalConormalInfinityIdealLineBundle s.ker) i j
    (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport_chart_isPullback s.ker U)
    (Conormal.InfinityChartIdeal.BundleCycles.conormalInfinityChartIdealIso s.ker U) n hp d hd α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.TopDegree.BundleCycles
