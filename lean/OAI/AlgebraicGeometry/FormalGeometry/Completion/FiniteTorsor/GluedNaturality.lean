import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.SectionToGlued
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseCoverFunctoriality

/-! # Glued Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: the section-to-glued-scheme map is a morphism of actual sheaves

Representing morphisms commute with restriction on the pulled-back affine
cover. Uniqueness of scheme gluing then proves naturality on the whole site.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} {ℓ n : ℕ} [NeZero (ℓ ^ n)]
  (E : App.Construction.FiniteCoefficientExtension ℓ n X) {V W : X.ProEt}

theorem App.Construction.FiniteCoefficientExtension.localSectionMap_restrict (g : V ⟶ W) (s : E.Fiber W) (i : X.directedAffineCover.I₀) :
    Affine.BaseCoverFunctoriality.Construction.affineBaseCoverChange g i ≫ E.localSectionMap W s i =
      E.localSectionMap V (E.restrict g s) i := by
  unfold App.Construction.FiniteCoefficientExtension.localSectionMap
  erw [SliceSectionMaps.Construction.sliceSectionMap_naturality E.fiberPresheaf
    (E.affineSliceRepresentative ((GluingData.Construction.proEtaleDirectedAffineDiagram X).obj i))
    (Affine.BaseCoverFunctoriality.Construction.affineBaseCoverChangeSlice g i)]
  congr 1
  change E.fiberPresheaf.map (Affine.BaseCoverFunctoriality.Construction.affineBaseCoverChange g i).op
      (E.fiberPresheaf.map (Affine.BaseCover.Construction.affineBaseCoverProjection W i).op s) =
    E.fiberPresheaf.map (Affine.BaseCover.Construction.affineBaseCoverProjection V i).op (E.fiberPresheaf.map g.op s)
  erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  rw [← op_comp, ← op_comp, Affine.BaseCoverFunctoriality.Construction.affineBaseCoverChange_projection]

theorem App.Construction.FiniteCoefficientExtension.sectionToGluedScheme_naturality (g : V ⟶ W) (s : E.Fiber W) :
    g.left ≫ E.sectionToGluedScheme W s = E.sectionToGluedScheme V (E.restrict g s) := by
  apply (Affine.BaseCover.Construction.affineBaseCover V).hom_ext
  intro i
  have hp := congrArg (fun k => k.left) (Affine.BaseCoverFunctoriality.Construction.affineBaseCoverChange_projection g i)
  change (Affine.BaseCoverFunctoriality.Construction.affineBaseCoverChange g i).left ≫ (Affine.BaseCover.Construction.affineBaseCover W).f i =
    (Affine.BaseCover.Construction.affineBaseCover V).f i ≫ g.left at hp
  rw [← Category.assoc, ← hp, Category.assoc, App.Construction.FiniteCoefficientExtension.sectionToGluedScheme_restrict]
  change (Affine.BaseCoverFunctoriality.Construction.affineBaseCoverChange g i).left ≫
      ((E.localSectionMap W s i).left ≫ colimit.ι E.relativeGluingData.functor i) = _
  rw [← Category.assoc]
  have hs := congrArg (fun k => k.left) (E.localSectionMap_restrict g s i)
  change (Affine.BaseCoverFunctoriality.Construction.affineBaseCoverChange g i).left ≫ (E.localSectionMap W s i).left =
    (E.localSectionMap V (E.restrict g s) i).left at hs
  rw [hs]
  exact (E.sectionToGluedScheme_restrict V (E.restrict g s) i).symm

/-- The actual site maps assigned to sections commute with every restriction. -/
theorem App.Construction.FiniteCoefficientExtension.sectionToGlued_naturality (g : V ⟶ W) (s : E.Fiber W) :
    g ≫ E.sectionToGlued W s = E.sectionToGlued V (E.restrict g s) :=
  MorphismProperty.Over.Hom.ext (E.sectionToGluedScheme_naturality g s)

/-- The resulting natural transformation to the actual representable presheaf. -/
def App.Construction.FiniteCoefficientExtension.sectionToGluedPresheaf : E.fiberPresheaf ⟶ uliftYoneda.{u + 1}.obj E.gluedProEt where
  app W := ↾fun s => ⟨E.sectionToGlued W.unop s⟩
  naturality W V g := by
    ext s
    apply ULift.ext
    exact (E.sectionToGlued_naturality g.unop s).symm

/-- The sheaf represented by the actual glued finite étale scheme. -/
def App.Construction.FiniteCoefficientExtension.gluedRepresentableSheaf : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  ⟨uliftYoneda.{u + 1}.obj E.gluedProEt, (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)⟩

/-- The comparison morphism between the original torsor and the actual represented sheaf. -/
def App.Construction.FiniteCoefficientExtension.sectionToGluedSheafHom : E.fiberSheaf ⟶ E.gluedRepresentableSheaf :=
  ⟨E.sectionToGluedPresheaf⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
