import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.GenericField
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image

/-! # Component Factor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ComponentFactor

noncomputable section

/-! An integral source maps into one actual open component of a smooth
projective presentation. The factorization preserves smoothness. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

variable {Z : Scheme} [IsIntegral Z] (Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : Z ⟶ Y.carrier)

def component : irreducibleComponents Y.carrier := Y.supportComponent (CycleClass.Geometric.StratumClosure.integralImageClosure f)

theorem range_subset : Set.range f ⊆ Set.range (Y.componentInclusion (component Y f)) := by
  rw [Y.componentInclusion_range]
  exact Set.Subset.trans subset_closure (Y.support_subset_component (CycleClass.Geometric.StratumClosure.integralImageClosure f))

def map : Z ⟶ (Y.componentVariety (component Y f)).carrier :=
  IsOpenImmersion.lift (Y.componentInclusion (component Y f)) f (range_subset Y f)

theorem fac : map Y f ≫ Y.componentInclusion (component Y f) = f :=
  IsOpenImmersion.lift_fac _ _ _

instance [Smooth f] : Smooth (map Y f) :=
  MorphismProperty.of_isPullback
    (IsOpenImmersion.isPullback_lift_id f (Y.componentInclusion (component Y f)) (range_subset Y f)).flip
    (inferInstance : Smooth f)

theorem generic_coheight [Smooth f] : coheight (f (genericPoint Z)) = 0 := by
  have he := ProjectionFormula.Smooth.GenericField.genericPoint_image (map Y f)
  have hf := congrArg (fun g : Z ⟶ Y.carrier => g (genericPoint Z)) (fac Y f)
  change Y.componentInclusion (component Y f) (map Y f (genericPoint Z)) = f (genericPoint Z) at hf
  rw [he] at hf
  rw [← hf, coheight_eq_of_isOpenImmersion (Y.componentInclusion (component Y f))]
  exact coheight_eq_zero.mpr (fun y _ => genericPoint_specializes y)

def overMap {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    (g : X.toOver ⟶ Y.toOver) : X.toOver ⟶ (Y.componentVariety (component (Z := X.carrier) Y g.left)).toOver :=
  Over.homMk (map (Z := X.carrier) Y g.left) (by
    change map (Z := X.carrier) Y g.left ≫
      (Y.componentVariety (component (Z := X.carrier) Y g.left)).structureMap = X.structureMap
    rw [← Y.componentInclusion_over, ← Category.assoc, fac]
    exact g.w)

theorem overMap_fac {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    (g : X.toOver ⟶ Y.toOver) :
    overMap Y g ≫ Component.Image.inclusion Y (component (Z := X.carrier) Y g.left) = g := by
  apply Over.OverMorphism.ext
  exact fac (Z := X.carrier) Y g.left

instance {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    (g : X.toOver ⟶ Y.toOver) [Smooth g.left] : Smooth (overMap Y g).left := by
  change Smooth (map (Z := X.carrier) Y g.left)
  infer_instance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ComponentFactor
