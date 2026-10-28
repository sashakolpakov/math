import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SectionAffineSpaceCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.GraphNormalCone

/-! # Affine Space Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.AffineSpaceCharts.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: affine-space bundle charts for the actual graph conormal projection -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

theorem graphConormalProjection_support :
    Conormal.SupportCover.BundleCycles.globalConormalToSupport (OpenAmbient.BundleCycles.graph f).ker ≫ inv (OpenAmbient.BundleCycles.graph f).toImage = Global.GraphNormalCone.BundleCycles.graphConormalProjection f := by
  have h : (OpenAmbient.BundleCycles.graph f).imageι ≫ OpenAmbient.BundleCycles.graphFirstProjection f = inv (OpenAmbient.BundleCycles.graph f).toImage := by
    apply (cancel_epi (OpenAmbient.BundleCycles.graph f).toImage).mp
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, OpenAmbient.BundleCycles.graph_firstProjection, IsIso.hom_inv_id]
  change _ = Conormal.DiagramGluing.BundleCycles.globalConormalSpectrumProjection (OpenAmbient.BundleCycles.graph f).ker ≫ OpenAmbient.BundleCycles.graphFirstProjection f
  rw [← Conormal.SupportCover.BundleCycles.globalConormalToSupport_toBase, Category.assoc, h]

theorem graphConormal_exists_affineSpaceChart (x : X.carrier) :
    ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ X.carrier) (ι : Type) (_ : Finite ι)
      (j : AffineSpace ι (Spec B) ⟶ Conormal.DiagramGluing.BundleCycles.globalConormalSpectrum (OpenAmbient.BundleCycles.graph f).ker),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ x ∈ Set.range i ∧
      IsPullback (AffineSpace ι (Spec B) ↘ Spec B) j i (Global.GraphNormalCone.BundleCycles.graphConormalProjection f) := by
  obtain ⟨B, i, ι, hι, j, hi, hj, hx, hsq⟩ := Global.SectionAffineSpaceCharts.BundleCycles.globalSection_exists_affineSpaceChart
    (OpenAmbient.BundleCycles.graphFirstProjection f) (OpenAmbient.BundleCycles.graph f) (OpenAmbient.BundleCycles.graph_firstProjection f) ((OpenAmbient.BundleCycles.graph f).toImage x)
  let i' := i ≫ inv (OpenAmbient.BundleCycles.graph f).toImage
  have hi' : IsOpenImmersion i' := @IsOpenImmersion.comp _ _ _ i (inv (OpenAmbient.BundleCycles.graph f).toImage)
    hi inferInstance
  refine ⟨B, i', ι, hι, j, hi', hj, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hx
    refine ⟨z, ?_⟩
    have h := congrArg (fun g => g x) (IsIso.hom_inv_id (OpenAmbient.BundleCycles.graph f).toImage)
    exact (congrArg (inv (OpenAmbient.BundleCycles.graph f).toImage) hz).trans h
  · apply hsq.of_iso (.refl _) (.refl _) (.refl _) (asIso (OpenAmbient.BundleCycles.graph f).toImage).symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · exact (Category.id_comp i').symm
    · exact (graphConormalProjection_support f).trans (Category.id_comp _).symm

end

/-! # LineBundleCycles: actual affine-space charts for the graph normal-cone projection -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

theorem graphNormalConeEquiv_inv_toSource :
    (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).inv ≫ (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker ≫ OpenAmbient.BundleCycles.graphFirstProjection f) =
      Global.GraphNormalCone.BundleCycles.graphConormalProjection f := by
  apply (cancel_epi (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv_toSource]

theorem graphNormalCone_exists_affineSpaceChart (x : X.carrier) :
    ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ X.carrier) (ι : Type) (_ : Finite ι)
      (j : AffineSpace ι (Spec B) ⟶ Global.SpecialFiber.BundleCycles.globalSpecialFiber (OpenAmbient.BundleCycles.graph f).ker),
      IsOpenImmersion i ∧ IsOpenImmersion j ∧ x ∈ Set.range i ∧
      IsPullback (AffineSpace ι (Spec B) ↘ Spec B) j i
        (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection (OpenAmbient.BundleCycles.graph f).ker ≫ OpenAmbient.BundleCycles.graphFirstProjection f) := by
  obtain ⟨B, i, ι, hι, j, hi, hj, hx, hsq⟩ := graphConormal_exists_affineSpaceChart f x
  let j' := j ≫ (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).inv
  have hj' : IsOpenImmersion j' := @IsOpenImmersion.comp _ _ _ j (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).inv hj inferInstance
  refine ⟨B, i, ι, hι, j', hi, hj', hx, ?_⟩
  apply hsq.of_iso (.refl _) (.refl _) (Global.GraphNormalCone.BundleCycles.graphNormalConeEquiv f).symm (.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact (Category.id_comp j').symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact (Category.comp_id _).trans (graphNormalConeEquiv_inv_toSource f).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.AffineSpaceCharts.BundleCycles
