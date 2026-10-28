import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GluedNaturality

/-! # Glued Charts -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: the global torsor comparison on each affine chart

If a site object maps into an affine base open, the global section map
is the local representing map followed by the chart inclusion. The
relative-gluing pullback square identifies all maps into that chart.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} {ℓ n : ℕ} [NeZero (ℓ ^ n)]
  (E : App.Construction.FiniteCoefficientExtension ℓ n X) {W : X.ProEt}

/-- The inclusion of a local representative into the global representative, in the actual site. -/
def App.Construction.FiniteCoefficientExtension.gluedChartInclusion (i : X.directedAffineCover.I₀) :
    (E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)).left ⟶ E.gluedProEt :=
  MorphismProperty.Over.homMk (colimit.ι E.relativeGluingData.functor i) (by
    exact (E.relativeGluingData.ι_toBase i).trans (MorphismProperty.Over.w
      (E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)).hom))

theorem App.Construction.FiniteCoefficientExtension.sectionToGlued_restrict (W : X.ProEt) (s : E.Fiber W)
    (i : X.directedAffineCover.I₀) :
    Affine.BaseCover.Construction.affineBaseCoverProjection W i ≫ E.sectionToGlued W s =
      E.localSectionMap W s i ≫ E.gluedChartInclusion i :=
  MorphismProperty.Over.Hom.ext (E.sectionToGluedScheme_restrict W s i)

/-- On an object over an affine open, the global map is its actual local representing map. -/
theorem App.Construction.FiniteCoefficientExtension.sectionToGlued_on_chart (i : X.directedAffineCover.I₀)
    (a : W ⟶ (GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) (s : E.Fiber W) :
    E.sectionToGlued W s =
      SliceSectionMaps.Construction.sliceSectionMap E.fiberPresheaf
        (E.affineSliceRepresentative ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i))
        (Over.mk a) s ≫ E.gluedChartInclusion i := by
  have h := congrArg (fun k => Affine.BaseCoverFunctoriality.Construction.affineBaseCoverSection i a ≫ k)
    (E.sectionToGlued_restrict W s i)
  rw [← Category.assoc, Affine.BaseCoverFunctoriality.Construction.affineBaseCoverSection_projection, Category.id_comp,
    ← Category.assoc] at h
  rw [h]
  congr 1
  unfold App.Construction.FiniteCoefficientExtension.localSectionMap
  erw [SliceSectionMaps.Construction.sliceSectionMap_naturality E.fiberPresheaf
    (E.affineSliceRepresentative ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i))
    (Affine.BaseCoverFunctoriality.Construction.affineBaseCoverSectionSlice i a)]
  congr 1
  change E.fiberPresheaf.map (Affine.BaseCoverFunctoriality.Construction.affineBaseCoverSection i a).op
      (E.fiberPresheaf.map (Affine.BaseCover.Construction.affineBaseCoverProjection W i).op s) = s
  erw [← Functor.map_comp_apply]
  rw [← op_comp, Affine.BaseCoverFunctoriality.Construction.affineBaseCoverSection_projection, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The pullback property of the chart lifts every global map over its affine base open. -/
def App.Construction.FiniteCoefficientExtension.gluedChartLift (i : X.directedAffineCover.I₀)
    (a : W ⟶ (GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) (b : W ⟶ E.gluedProEt) :
    Over.mk a ⟶ E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) := by
  let h := E.relativeGluingData.isPullback_natTrans_ι_toBase i
  let hc : a.left ≫ X.directedAffineCover.f i = b.left ≫ E.relativeGluingData.toBase :=
    (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm
  let f := h.lift a.left b.left hc
  have hf : f ≫ (E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)).hom.left =
      a.left := h.lift_fst _ _ _
  let g : W ⟶ (E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)).left :=
    MorphismProperty.Over.homMk f (by
      calc
        f ≫ (E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)).left.hom =
            f ≫ (E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)).hom.left ≫
              ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i).hom := by
                rw [MorphismProperty.Over.w]
        _ = a.left ≫ ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i).hom := by
          rw [← Category.assoc, hf]
        _ = W.hom := MorphismProperty.Over.w a)
  exact Over.homMk g (MorphismProperty.Over.Hom.ext hf)

theorem App.Construction.FiniteCoefficientExtension.gluedChartLift_inclusion (i : X.directedAffineCover.I₀)
    (a : W ⟶ (GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) (b : W ⟶ E.gluedProEt) :
    (E.gluedChartLift i a b).left ≫ E.gluedChartInclusion i = b := by
  apply MorphismProperty.Over.Hom.ext
  exact (E.relativeGluingData.isPullback_natTrans_ι_toBase i).lift_snd _ _ _

theorem App.Construction.FiniteCoefficientExtension.gluedChartInclusion_cancel (i : X.directedAffineCover.I₀)
    (a b : W ⟶ (E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)).left)
    (h : a ≫ E.gluedChartInclusion i = b ≫ E.gluedChartInclusion i) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (colimit.ι E.relativeGluingData.functor i)).mp
  exact congrArg (fun k => k.left) h

/-- The global section map is bijective on every object lying over an affine base open. -/
theorem App.Construction.FiniteCoefficientExtension.sectionToGlued_bijective_on_chart (i : X.directedAffineCover.I₀)
    (a : W ⟶ (GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i) :
    Function.Bijective (E.sectionToGlued W) := by
  let r := E.affineSliceRepresentative ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)
  constructor
  · intro s t h
    rw [E.sectionToGlued_on_chart i a s, E.sectionToGlued_on_chart i a t] at h
    have he := E.gluedChartInclusion_cancel i _ _ h
    exact (SliceSectionMaps.Construction.sliceSectionMap_section E.fiberPresheaf r (Over.mk a) s).symm.trans
      ((congrArg (fun f => E.fiberPresheaf.map f.op (SliceRepresentativeMaps.Construction.sliceUniversalSection E.fiberPresheaf r))
        he).trans (SliceSectionMaps.Construction.sliceSectionMap_section E.fiberPresheaf r (Over.mk a) t))
  · intro b
    let f := E.gluedChartLift i a b
    refine ⟨r.homEquiv f, ?_⟩
    rw [E.sectionToGlued_on_chart i a]
    change ((r.homEquiv (X := Over.mk a)).symm (r.homEquiv f)).left ≫ _ = _
    rw [r.homEquiv.symm_apply_apply]
    exact E.gluedChartLift_inclusion i a b

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
