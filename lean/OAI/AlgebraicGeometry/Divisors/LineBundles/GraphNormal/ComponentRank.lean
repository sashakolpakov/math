import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.TargetComponent
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.RelativeOpenSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Section.AffineNeighborhoodInside
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SectionChartConormalRank
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.AffineSpaceRankChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.Conormal
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.FiberRankOpen

/-! # Component Rank -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentRank.BundleCycles

noncomputable section

section

/-! The actual graph-normal rank at a source point is the dimension
of the target component containing its image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem graphNormalFiberRank_at_targetComponent {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (D : irreducibleComponents Y.carrier) (x : X.carrier)
    (hxD : f.left x ∈ Set.range (Y.componentInclusion D)) :
    AffineBundle.FiberRank.Cycles.affineBundleFiberRank (Graph.Chow.BundleCycles.graphNormalProjection f) X.structureMap x =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Y.componentVariety D).structureMap := by
  let n := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Y.componentVariety D).structureMap
  let jD := Graph.TargetComponent.BundleCycles.graphTargetComponentInclusion f D
  let qD := Graph.TargetComponent.BundleCycles.graphTargetComponentFirst f D
  let : IsOpenImmersion jD := Graph.TargetComponent.BundleCycles.graphTargetComponentInclusion_isOpenImmersion f D
  let : SmoothOfRelativeDimension n qD := Graph.TargetComponent.BundleCycles.graphTargetComponentFirst_relativeDimension f D
  have hxW : Graph.OpenAmbient.BundleCycles.graph f x ∈ jD.opensRange := by
    change Graph.OpenAmbient.BundleCycles.graph f x ∈ Set.range (Graph.TargetComponent.BundleCycles.graphTargetComponentInclusion f D)
    rw [Graph.TargetComponent.BundleCycles.graphTargetComponentInclusion_range]
    change Graph.OpenAmbient.BundleCycles.graphSecondProjection f (Graph.OpenAmbient.BundleCycles.graph f x) ∈ Set.range (Y.componentInclusion D)
    have hg := congrArg (fun a => a x) (Graph.OpenAmbient.BundleCycles.graph_secondProjection f)
    exact hg.symm ▸ hxD
  obtain ⟨U, V, hU, hV, hx, hVU, hUV, hUW⟩ := Section.AffineNeighborhoodInside.BundleCycles.section_exists_affineNeighborhoods_inside
    (Graph.OpenAmbient.BundleCycles.graphFirstProjection f) (Graph.OpenAmbient.BundleCycles.graph f) (Graph.OpenAmbient.BundleCycles.graph_firstProjection f) x jD.opensRange hxW
  let q := Section.OpenRestriction.BundleCycles.sectionOpenProjection (Graph.OpenAmbient.BundleCycles.graphFirstProjection f) U V hUV
  have hUj : Set.range U.ι ⊆ Set.range jD := by
    rw [Scheme.Opens.range_ι]
    exact hUW
  let j : U.toScheme ⟶ Graph.TargetComponent.BundleCycles.graphTargetComponent f D := IsOpenImmersion.lift jD U.ι hUj
  have hj : j ≫ jD = U.ι := IsOpenImmersion.lift_fac _ _ _
  let : IsOpenImmersion (j ≫ jD) := hj.symm ▸ inferInstance
  let : IsOpenImmersion j := IsOpenImmersion.of_comp j jD
  have hsq : q ≫ V.ι = j ≫ qD := by
    change q ≫ V.ι = j ≫ (jD ≫ Graph.OpenAmbient.BundleCycles.graphFirstProjection f)
    rw [← Category.assoc, hj]
    exact Section.OpenRestriction.BundleCycles.sectionOpenProjection_ι (Graph.OpenAmbient.BundleCycles.graphFirstProjection f) U V hUV
  have hrel : SmoothOfRelativeDimension n q := Smooth.RelativeOpenSquare.BundleCycles.smoothRelativeDimension_openSquare qD n q V.ι j hsq
  let W : (Graph.OpenAmbient.BundleCycles.graphAmbient f).AffineZariskiSite := ⟨U, hU⟩
  obtain ⟨hf, hp⟩ := Affine.SectionChartConormal.BundleCycles.affineSectionChart_conormal_finite_projective (Graph.OpenAmbient.BundleCycles.graphFirstProjection f)
    (Graph.OpenAmbient.BundleCycles.graph f) (Graph.OpenAmbient.BundleCycles.graph_firstProjection f) U V hU hV hVU hUV
  let : Module.Finite (Γ(Graph.OpenAmbient.BundleCycles.graphAmbient f, W.1) ⧸ (Graph.OpenAmbient.BundleCycles.graph f).ker.ideal W) ((Graph.OpenAmbient.BundleCycles.graph f).ker.ideal W).Cotangent := hf
  let : Module.Projective (Γ(Graph.OpenAmbient.BundleCycles.graphAmbient f, W.1) ⧸ (Graph.OpenAmbient.BundleCycles.graph f).ker.ideal W) ((Graph.OpenAmbient.BundleCycles.graph f).ker.ideal W).Cotangent := hp
  have hz : (Graph.OpenAmbient.BundleCycles.graph f).toImage x ∈ (Support.Projection.BundleCycles.supportCoefficientChart (Graph.OpenAmbient.BundleCycles.graph f).ker W).opensRange := by
    rw [Support.Projection.BundleCycles.supportCoefficientChart_range]
    have he : (Graph.OpenAmbient.BundleCycles.graph f).ker.subschemeι ((Graph.OpenAmbient.BundleCycles.graph f).toImage x) = Graph.OpenAmbient.BundleCycles.graph f x :=
      congrArg (fun a => a x) (Graph.OpenAmbient.BundleCycles.graph f).toImage_imageι
    change (Graph.OpenAmbient.BundleCycles.graph f).ker.subschemeι ((Graph.OpenAmbient.BundleCycles.graph f).toImage x) ∈ U
    rw [he]
    exact hVU hx
  obtain ⟨a, ha⟩ := hz
  let a' : PrimeSpectrum (Γ(Graph.OpenAmbient.BundleCycles.graphAmbient f, W.1) ⧸ (Graph.OpenAmbient.BundleCycles.graph f).ker.ideal W) := a
  have ha' : Support.Projection.BundleCycles.supportCoefficientChart (Graph.OpenAmbient.BundleCycles.graph f).ker W a' = (Graph.OpenAmbient.BundleCycles.graph f).toImage x := ha
  have hrank : Module.rankAtStalk ((Graph.OpenAmbient.BundleCycles.graph f).ker.ideal W).Cotangent a' = n :=
    Affine.SectionChartConormalRank.BundleCycles.affineSectionChart_conormal_rank_of_restrictedDimension (Graph.OpenAmbient.BundleCycles.graphFirstProjection f) n
      (Graph.OpenAmbient.BundleCycles.graph f) (Graph.OpenAmbient.BundleCycles.graph_firstProjection f) U V hU hV hVU hUV hrel a'
  obtain ⟨B, i, ι, hι, k, hi, hk, ha'', hs, hn⟩ :=
    Conormal.AffineSpaceRankChart.BundleCycles.conormal_exists_affineSpaceChart_of_rank (Graph.OpenAmbient.BundleCycles.graph f).ker W a' n hrank
  let := hι
  let := hi
  let := hk
  obtain ⟨b, hb⟩ := ha''
  have hix : i b = (Graph.OpenAmbient.BundleCycles.graph f).toImage x := hb.trans ha'
  have H := AffineBundle.FiberRank.Cycles.affineBundleFiberRank_openChart (Conormal.SupportCover.BundleCycles.globalConormalToSupport (Graph.OpenAmbient.BundleCycles.graph f).ker)
    (Graph.Conormal.BundleCycles.graphCenterStructureMap f) i ι k hs.w b
  rw [hix, hn] at H
  have H' := AffineBundle.FiberRankOpen.Cycles.affineBundleFiberRank_openSquare (Conormal.SupportCover.BundleCycles.globalConormalToSupport (Graph.OpenAmbient.BundleCycles.graph f).ker)
    (Graph.Chow.BundleCycles.graphNormalProjection f) (Graph.OpenAmbient.BundleCycles.graph f).toImage (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).hom
    (Graph.Conormal.BundleCycles.graphNormalConeEquiv_center_square f) (Graph.Conormal.BundleCycles.graphCenterStructureMap f) x
  rw [Graph.Conormal.BundleCycles.graphToCenter_structure] at H'
  exact H'.symm.trans H

end

/-! The actual normal bundle over each integral source component has
rank equal to the dimension of the component receiving its image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

theorem graphNormalComponent_hasAffineSpaceChartsOfRank {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (C : irreducibleComponents X.carrier) :
    AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank (pullback.snd (Graph.Chow.BundleCycles.graphNormalProjection f) (X.componentInclusion C))
      (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Y.componentVariety (LineBundles.Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)).structureMap) := by
  let i := X.componentInclusion C
  let : IsOpenImmersion i := X.componentInclusion_isOpenImmersion C
  let : AlgebraicGeometry.IsNoetherian (pullback (Graph.Chow.BundleCycles.graphNormalProjection f) i : Scheme) :=
    Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (pullback.fst (Graph.Chow.BundleCycles.graphNormalProjection f) i)
  let q := pullback.snd (Graph.Chow.BundleCycles.graphNormalProjection f) i
  let : GeometricallyIntegral q := inferInstanceAs (GeometricallyIntegral (pullback.snd (Graph.Chow.BundleCycles.graphNormalProjection f) i))
  apply AffineBundle.FiberRank.Cycles.affineBundle_hasChartsOfRank_of_fiberRank q (X.componentVariety C).structureMap
    ((Affine.SpaceChartBaseChange.BundleCycles.graphNormalCone_hasAffineSpaceCharts f).baseChange i)
  intro u
  have hu : f.left (i u) ∈ Set.range (Y.componentInclusion (LineBundles.Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)) :=
    LineBundles.Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent_range f C ⟨u, rfl⟩
  have H := graphNormalFiberRank_at_targetComponent f (LineBundles.Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C) (i u) hu
  have H' := AffineBundle.FiberRankOpen.Cycles.affineBundleFiberRank_openSquare (Graph.Chow.BundleCycles.graphNormalProjection f) q i
    (pullback.fst (Graph.Chow.BundleCycles.graphNormalProjection f) i) (pullback.condition.symm) X.structureMap u
  have hi : i ≫ X.structureMap = (X.componentVariety C).structureMap := X.componentInclusion_over C
  rw [hi] at H'
  exact H'.symm.trans H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentRank.BundleCycles
