import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Bilinear
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.ComponentMaps
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.IntegralCycleDescent
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Clopen Cycles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenCycles

noncomputable section

/-! Open restriction of native cycles in every codimension preserves
rational equivalence and commutes with smooth inverse image. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle

theorem flat_at_point {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n p : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (a : Y.RationalDimensionCycle p) (A : X.DimensionCycleSupport p) (B : Y.DimensionCycleSupport p)
    (h : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : ProjectionFormula.Smooth.Cycle.flatMap f p a A = a B := by
  rw [ProjectionFormula.Smooth.Cycle.flatMap_apply f p m n]
  have he (D : Y.DimensionCycleSupport p) : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint D.val ↔ B = D := by
    rw [h]
    constructor
    · intro hd
      exact Subtype.ext (irreducibleSetEquivPoints.injective hd)
    · rintro rfl
      rfl
  simp only [he, Finsupp.sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hb : B ∈ a.support
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb, Finsupp.notMem_support_iff.mp hb]

theorem flat_restrict {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left]
    (m p : ℕ) [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) : ProjectionFormula.Smooth.Cycle.flatMap i p a = Clopen.CycleMaps.restrict i m p a := by
  ext A
  exact flat_at_point i m m p a A (Clopen.Cycle.supportImage i m p A) (Clopen.Cycle.image_point i A.val).symm

theorem restrict_flatMap {V X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n p : ℕ) [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] (a : Y.RationalDimensionCycle p) :
    Clopen.CycleMaps.restrict i m p (ProjectionFormula.Smooth.Cycle.flatMap f p a) = ProjectionFormula.Smooth.Cycle.flatMap (i ≫ f) p a := by
  let : Smooth (i ≫ f).left := by change Smooth (i.left ≫ f.left); infer_instance
  ext A
  rw [Clopen.CycleMaps.restrict_apply, ProjectionFormula.Smooth.Cycle.flatMap_apply f p m n, ProjectionFormula.Smooth.Cycle.flatMap_apply (i ≫ f) p m n]
  have he : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint (Clopen.Cycle.supportImage i m p A).val) = (i ≫ f).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) := by
    change f.left (CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i A.val)) = _
    rw [Clopen.Cycle.image_point]
    rfl
  exact congrArg (fun y : Y.carrier => a.sum (fun B r => r * if y = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0)) he

theorem integral_factor_iso {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral V.carrier]
    (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] : IsIso (Integral.ComponentFactor.overMap X i).left := by
  let C := Integral.ComponentFactor.component (Z := V.carrier) X i.left
  let q : V.carrier ⟶ (X.componentVariety C).carrier := (Integral.ComponentFactor.overMap X i).left
  have hq : q ≫ X.componentInclusion C = i.left := Integral.ComponentFactor.fac (Z := V.carrier) X i.left
  let : IsOpenImmersion (q ≫ X.componentInclusion C) := hq.symm ▸ inferInstance
  let : IsOpenImmersion q := IsOpenImmersion.of_comp q (X.componentInclusion C)
  let : IsProper q := ProperCycleLinearity.morphism_isProper (Integral.ComponentFactor.overMap X i)
  let : Surjective q := ⟨fun y =>
    (genericPoint_specializes y).mem_closed q.isClosedMap.isClosed_range
      ⟨genericPoint V.carrier, ProjectionFormula.Smooth.GenericField.genericPoint_image q⟩⟩
  exact (isIso_iff_isOpenImmersion_and_surjective q).mpr ⟨inferInstance, inferInstance⟩

theorem iso_geometricallyIntegral {A B : Scheme.{0}} (f : A ⟶ B) [IsIso f] : GeometricallyIntegral f := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (@IsIntegral : Scheme.{0} → Prop) :=
    ⟨fun e h => by let _ := h; exact IsIntegral.of_isIso e.hom⟩
  refine ⟨(geometrically_iff_of_isClosedUnderIsomorphisms (P := @IsIntegral) (f := f)).mpr ?_⟩
  intro K _ g
  exact IsIntegral.of_isIso (inv (pullback.snd f g))

theorem restrict_relations {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left]
    (m p : ℕ) [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap] :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p ≤ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences V p).comap (Clopen.CycleMaps.restrict i m p) := by
  intro a ha
  change Clopen.CycleMaps.restrict i m p a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences V p
  rw [← flat_restrict i m p a]
  apply (Component.Principal.CycleDecomposition.relations_iff V m p _).mpr
  intro C
  let Z := (V.componentVariety C).presentation
  let g : Z.toOver ⟶ X.toOver := Component.Image.inclusion V C ≫ i
  let D := Integral.ComponentFactor.component (Z := Z.carrier) X g.left
  let : SmoothOfRelativeDimension m Z.structureMap := Component.Image.component_relativeDimension V m C
  let : SmoothOfRelativeDimension m (X.componentVariety D).structureMap := Component.Image.component_relativeDimension X m D
  let : IsOpenImmersion g.left := by change IsOpenImmersion (V.componentInclusion C ≫ i.left); infer_instance
  let : IsIso (Integral.ComponentFactor.overMap X g).left := integral_factor_iso g
  let : GeometricallyIntegral (show Z.carrier ⟶ (X.componentVariety D).carrier from
      (Integral.ComponentFactor.overMap X g).left) := iso_geometricallyIntegral _
  rw [ProjectionFormula.Smooth.CycleComponents.restrict_flatMap i m m p C, ProjectionFormula.Smooth.CycleComponents.flatMap_factor g m m p]
  exact ProjectionFormula.Smooth.IntegralCycleDescent.preserves_relations (Integral.ComponentFactor.overMap X g) m m p
    (Component.Principal.restrict_preserves_relations X D p ha)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenCycles
