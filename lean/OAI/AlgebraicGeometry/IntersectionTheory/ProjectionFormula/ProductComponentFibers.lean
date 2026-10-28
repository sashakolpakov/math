import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedGeometricIntegral
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ComponentFactor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDivisorPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.IntegralOpenSource
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Product Component Fibers -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductComponentFibers

noncomputable section

/-! Each integral component of a smooth projective product has geometrically
integral fibers over the target component it reaches. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ComponentFactor

theorem snd_geometricallyIntegral {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (P : ProperCycleLinearity.ProductPresentation X Y) (C : irreducibleComponents P.space.carrier) :
    GeometricallyIntegral (Integral.ComponentFactor.overMap Y (Component.Image.inclusion P.space C ≫ P.snd)).left := by
  let V := (P.space.componentVariety C).presentation
  let gX : V.toOver ⟶ X.toOver := Component.Image.inclusion P.space C ≫ P.fst
  let gY : V.toOver ⟶ Y.toOver := Component.Image.inclusion P.space C ≫ P.snd
  let D := Integral.ComponentFactor.component (Z := V.carrier) X gX.left
  let E := Integral.ComponentFactor.component (Z := V.carrier) Y gY.left
  let a : V.carrier ⟶ (X.componentVariety D).carrier := (Integral.ComponentFactor.overMap X gX).left
  let q : V.carrier ⟶ (Y.componentVariety E).carrier := (Integral.ComponentFactor.overMap Y gY).left
  let πX : P.space.carrier ⟶ X.carrier := P.fst.left
  let πY : P.space.carrier ⟶ Y.carrier := P.snd.left
  let S := pullback πX (X.componentInclusion D)
  let u : S ⟶ P.space.carrier := pullback.fst _ _
  let p : S ⟶ Y.carrier := u ≫ πY
  have hP : IsPullback πX πY X.structureMap Y.structureMap :=
    Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk P.fst P.snd) P.isLimit
  have hS : IsPullback p (pullback.snd πX (X.componentInclusion D))
      Y.structureMap (X.componentVariety D).structureMap := by
    have h := (IsPullback.of_hasPullback πX (X.componentInclusion D)).paste_horiz hP.flip
    rw [X.componentInclusion_over D] at h
    exact h
  let : GeometricallyIntegral (X.componentVariety D).structureMap :=
    ClosedGeometricIntegral.geometricallyIntegral (X.componentVariety D).structureMap
  let : GeometricallyIntegral p := MorphismProperty.of_isPullback hS.flip inferInstance
  have ha : P.space.componentInclusion C ≫ πX = a ≫ X.componentInclusion D :=
    (Integral.ComponentFactor.fac (Z := V.carrier) X gX.left).symm
  let j : V.carrier ⟶ S := pullback.lift (P.space.componentInclusion C) a ha
  have hj : j ≫ u = P.space.componentInclusion C := pullback.lift_fst _ _ _
  let : IsOpenImmersion u := inferInstanceAs (IsOpenImmersion (pullback.fst πX (X.componentInclusion D)))
  let : IsOpenImmersion (j ≫ u) := hj.symm ▸ inferInstance
  let : IsOpenImmersion j := IsOpenImmersion.of_comp j u
  let : Smooth πY := ProductDivisorPullback.snd_smooth P
  let : Smooth gY.left := by
    change Smooth (P.space.componentInclusion C ≫ πY)
    infer_instance
  let : Smooth q := inferInstanceAs (Smooth (Integral.ComponentFactor.overMap Y gY).left)
  let : IsProper q := ProperCycleLinearity.morphism_isProper (Integral.ComponentFactor.overMap Y gY)
  let : Surjective q := ⟨fun y =>
    (genericPoint_specializes y).mem_closed q.isClosedMap.isClosed_range
      ⟨genericPoint V.carrier, ProjectionFormula.Smooth.GenericField.genericPoint_image q⟩⟩
  have hq : q ≫ Y.componentInclusion E = j ≫ p := by
    rw [show j ≫ p = P.space.componentInclusion C ≫ πY by
      change j ≫ u ≫ πY = _
      rw [← Category.assoc, hj]]
    exact Integral.ComponentFactor.fac (Z := V.carrier) Y gY.left
  exact Divisors.LineBundles.Geometric.IntegralOpenSource.BundleCycles.geometricallyIntegral_openSquare p q (Y.componentInclusion E) j hq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductComponentFibers
