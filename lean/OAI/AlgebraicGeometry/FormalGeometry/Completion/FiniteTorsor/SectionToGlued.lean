import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseCover
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceSectionMaps

/-! # Section To Glued -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: actual torsor sections give morphisms to the glued scheme

Represent each restricted section over the pulled-back affine cover. The
checked transition laws make these morphisms compatible, so ordinary scheme
gluing gives a morphism over the original base.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} {ℓ n : ℕ} [NeZero (ℓ ^ n)]
  (E : App.Construction.FiniteCoefficientExtension ℓ n X) (W : X.ProEt) (s : E.Fiber W)

/-- The local morphism representing the restriction of an actual torsor section. -/
def App.Construction.FiniteCoefficientExtension.localSectionMap (i : X.directedAffineCover.I₀) :
    Affine.BaseCover.Construction.affineBaseCoverObject W i ⟶ (E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)).left :=
  SliceSectionMaps.Construction.sliceSectionMap E.fiberPresheaf
    (E.affineSliceRepresentative ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i))
    (Affine.BaseCover.Construction.affineBaseCoverSlice W i) (E.restrict (Affine.BaseCover.Construction.affineBaseCoverProjection W i) s)

theorem App.Construction.FiniteCoefficientExtension.localSectionMap_over (i : X.directedAffineCover.I₀) :
    E.localSectionMap W s i ≫ (E.affineSliceObject ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i)).hom =
      Affine.BaseCover.Construction.affineBaseCoverToOpen W i := SliceSectionMaps.Construction.sliceSectionMap_over _ _ _ _

/-- The local section maps agree under the canonical affine transition morphisms. -/
theorem App.Construction.FiniteCoefficientExtension.localSectionMap_transition {i j : X.directedAffineCover.I₀} (h : i ⟶ j) :
    E.localSectionMap W s i ≫
        SliceRepresentativeMaps.Construction.sliceRepresentativeMap E.fiberPresheaf
          (E.affineSliceRepresentative ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i))
          (E.affineSliceRepresentative ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj j))
          ((GluingData.Construction.proEtaleDirectedAffineDiagram X).map h) =
      Affine.BaseCover.Construction.affineBaseCoverTransition W h ≫ E.localSectionMap W s j := by
  rw [App.Construction.FiniteCoefficientExtension.localSectionMap, SliceSectionMaps.Construction.sliceSectionMap_transition]
  change SliceSectionMaps.Construction.sliceSectionMap E.fiberPresheaf
      (E.affineSliceRepresentative ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj j))
      ((Over.map ((GluingData.Construction.proEtaleDirectedAffineDiagram X).map h)).obj (Affine.BaseCover.Construction.affineBaseCoverSlice W i)) _ = _
  rw [App.Construction.FiniteCoefficientExtension.localSectionMap]
  erw [SliceSectionMaps.Construction.sliceSectionMap_naturality E.fiberPresheaf
    (E.affineSliceRepresentative ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj j))
    (Affine.BaseCover.Construction.affineBaseCoverSliceTransition W h)]
  congr 1
  change E.fiberPresheaf.map (Affine.BaseCover.Construction.affineBaseCoverProjection W i).op s =
    E.fiberPresheaf.map (Affine.BaseCover.Construction.affineBaseCoverTransition W h).op
      (E.fiberPresheaf.map (Affine.BaseCover.Construction.affineBaseCoverProjection W j).op s)
  erw [← Functor.map_comp_apply]
  rw [← op_comp, Affine.BaseCover.Construction.affineBaseCoverTransition_projection]

/-- The local maps followed by their inclusions into the glued scheme. -/
def App.Construction.FiniteCoefficientExtension.localSectionToGlued (i : X.directedAffineCover.I₀) : (Affine.BaseCover.Construction.affineBaseCover W).X i ⟶ E.gluedScheme :=
  (E.localSectionMap W s i).left ≫ colimit.ι E.relativeGluingData.functor i

theorem App.Construction.FiniteCoefficientExtension.localSectionToGlued_transition {i j : X.directedAffineCover.I₀} (h : i ⟶ j) :
    (Affine.BaseCover.Construction.affineBaseCover W).trans h ≫ E.localSectionToGlued W s j = E.localSectionToGlued W s i := by
  change (Affine.BaseCover.Construction.affineBaseCoverTransition W h).left ≫
      ((E.localSectionMap W s j).left ≫ colimit.ι E.relativeGluingData.functor j) = _
  rw [← Category.assoc]
  have ht := congrArg (fun k => k.left) (E.localSectionMap_transition W s h)
  change (E.localSectionMap W s i).left ≫ E.relativeGluingData.functor.map h =
    (Affine.BaseCover.Construction.affineBaseCoverTransition W h).left ≫ (E.localSectionMap W s j).left at ht
  rw [← ht, Category.assoc, colimit.w]
  rfl

/-- The actual morphism obtained by gluing all local representing maps. -/
def App.Construction.FiniteCoefficientExtension.sectionToGluedScheme : W.left ⟶ E.gluedScheme :=
  (Affine.BaseCover.Construction.affineBaseCover W).glueMorphismsOfLocallyDirected (E.localSectionToGlued W s)
    (E.localSectionToGlued_transition W s)

theorem App.Construction.FiniteCoefficientExtension.sectionToGluedScheme_restrict (i : X.directedAffineCover.I₀) :
    (Affine.BaseCover.Construction.affineBaseCover W).f i ≫ E.sectionToGluedScheme W s = E.localSectionToGlued W s i :=
  (Affine.BaseCover.Construction.affineBaseCover W).map_glueMorphismsOfLocallyDirected _ _ i

/-- The glued section map respects the original structure morphism. -/
theorem App.Construction.FiniteCoefficientExtension.sectionToGluedScheme_over : E.sectionToGluedScheme W s ≫ E.gluedSchemeToBase = W.hom := by
  apply (Affine.BaseCover.Construction.affineBaseCover W).hom_ext
  intro i
  rw [← Category.assoc, App.Construction.FiniteCoefficientExtension.sectionToGluedScheme_restrict]
  change ((E.localSectionMap W s i).left ≫ colimit.ι E.relativeGluingData.functor i) ≫
    E.relativeGluingData.toBase = _
  rw [Category.assoc, E.relativeGluingData.ι_toBase, ← Category.assoc]
  have h := congrArg (fun k => k.left) (E.localSectionMap_over W s i)
  change (E.localSectionMap W s i).left ≫ E.relativeGluingData.natTrans.app i =
    pullback.snd W.hom (X.directedAffineCover.f i) at h
  rw [h]
  exact pullback.condition.symm

/-- Every actual torsor section gives a map to the glued object in the original site. -/
def App.Construction.FiniteCoefficientExtension.sectionToGlued : W ⟶ E.gluedProEt :=
  MorphismProperty.Over.homMk (E.sectionToGluedScheme W s) (E.sectionToGluedScheme_over W s)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
