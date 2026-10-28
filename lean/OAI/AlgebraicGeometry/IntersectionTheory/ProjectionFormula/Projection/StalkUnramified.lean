import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.LocalCoordinates
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.OverScalars
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AugmentedResidueMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FirstOrderUnramified
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TangentFinite

/-! # Stalk Unramified -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.StalkUnramified

noncomputable section

section

/-! The finite projection with first-order bases is formally
unramified on the actual stalks at the prescribed points. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] PointJetCoordinates.scalar

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
  (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier) (hp : p ≫ X.structureMap = 𝟙 _)
  (hspan : Submodule.span ℂ (Set.range (fun a => PointJetCoordinates.map X p hp (L a))) = ⊤)

theorem over : FiniteProjective.FromForms.map X m L h ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m =
    X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension := by
  rw [FiniteProjective.FromForms.over_base, X.embedding_over]

def stalk :
    letI := Stalk.PointAlgebra.scalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)
      (FiniteProjective.FromForms.map X m L h (p (IsLocalRing.closedPoint ℂ)))
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace m).presheaf.stalk (FiniteProjective.FromForms.map X m L h (p (IsLocalRing.closedPoint ℂ))) →ₐ[ℂ]
      X.carrier.presheaf.stalk (p (IsLocalRing.closedPoint ℂ)) :=
  Stalk.OverScalars.map (FiniteProjective.FromForms.map X m L h)
    (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)
    (over X m L h) (p (IsLocalRing.closedPoint ℂ))

include hspan in
theorem maximalIdeal :
    (IsLocalRing.maximalIdeal ((Foundations.Scheme.ProjectiveSpace.projectiveSpace m).presheaf.stalk
      (FiniteProjective.FromForms.map X m L h (p (IsLocalRing.closedPoint ℂ))))).map
        ((FiniteProjective.FromForms.map X m L h).stalkMap (p (IsLocalRing.closedPoint ℂ))).hom =
      IsLocalRing.maximalIdeal (X.carrier.presheaf.stalk (p (IsLocalRing.closedPoint ℂ))) := by
  let x := p (IsLocalRing.closedPoint ℂ)
  let π := FiniteProjective.FromForms.map X m L h
  let := Stalk.PointAlgebra.scalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) (π x)
  let g := StalkUnramified.stalk X m L h p
  let ε := Stalk.PointAlgebra.evaluation
    (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) p (PointJetCoordinates.over X p hp)
  let c := PointJetCoordinates.coordinate X p
  have hc := PointJetCoordinates.coordinate_mem X p
  let s := LocalCoordinates.sourceValue X m L x c hc
  obtain ⟨i, hi⟩ := h x
  let t := LocalCoordinates.targetCoordinate X m L h x i hi
  have hr : ε (s i) ≠ 0 :=
    ((LocalCoordinates.sourceValue_isUnit X m L x i hi c hc).map ε.toRingHom).ne_zero
  have hs : Submodule.span ℂ (Set.range (fun a => AugmentedCotangent.jet ε (s a))) = ⊤ := hspan
  have ht : ∀ a, s i * g (t a) = s a := by
    intro a
    rw [show g (t a) = π.stalkMap x (t a) from Stalk.OverScalars.apply _ _ _ _ _ _]
    exact LocalCoordinates.normalized X m L h x i hi c hc a
  have hg : IsLocalHom g.toRingHom := Stalk.OverScalars.isLocal _ _ _ _ _
  let := hg
  have he := FirstOrderUnramified.map_maximalIdeal_eq g ε s (s i) hr hs t ht
  rw [show g.toRingHom = (π.stalkMap x).hom from Stalk.OverScalars.ringHom _ _ _ _ _] at he
  exact he

include hspan in
theorem unramified :
    ((FiniteProjective.FromForms.map X m L h).stalkMap (p (IsLocalRing.closedPoint ℂ))).hom.FormallyUnramified := by
  let x := p (IsLocalRing.closedPoint ℂ)
  let π := FiniteProjective.FromForms.map X m L h
  let := Stalk.PointAlgebra.scalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) (π x)
  let g := StalkUnramified.stalk X m L h p
  let ε := Stalk.PointAlgebra.evaluation
    (X.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase X.ambientDimension) p (PointJetCoordinates.over X p hp)
  have hg : IsLocalHom g.toRingHom := Stalk.OverScalars.isLocal _ _ _ _ _
  let := hg
  have hmap : g.toRingHom = (π.stalkMap x).hom := Stalk.OverScalars.ringHom _ _ _ _ _
  rw [← hmap]
  let := g.toRingHom.toAlgebra
  let : Algebra.EssFiniteType ((Foundations.Scheme.ProjectiveSpace.projectiveSpace m).presheaf.stalk (π x)) (X.carrier.presheaf.stalk x) := by
    change g.toRingHom.EssFiniteType
    rw [hmap]
    exact LocallyOfFiniteType.stalkMap π x
  let := AugmentedResidueMap.separable ε g
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  change (IsLocalRing.maximalIdeal _).map g.toRingHom = _
  rw [hmap]
  exact StalkUnramified.maximalIdeal X m L h p hp hspan

end

/-! Unconditional existence of a finite linear projection that is
formally unramified on the stalks at any specified finite family of closed points. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Finite

theorem exists_points (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {ι : Type} [Finite ι] (p : ι → (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier))
    (hp : ∀ j, p j ≫ X.structureMap = 𝟙 _) :
    ∃ π : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m,
      π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap ∧ IsFinite π ∧
      ∀ j, (π.stalkMap (p j (IsLocalRing.closedPoint ℂ))).hom.FormallyUnramified := by
  obtain ⟨L, h, hover, hfinite, hbase⟩ := TangentFinite.Projection.exists_projection X m p hp
  refine ⟨FiniteProjective.FromForms.map X m L h, hover, hfinite, fun j => ?_⟩
  exact unramified X m L h (p j) (hp j) (hbase j).2

theorem exists_closed_points (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {ι : Type} [Finite ι] (x : ι → X.carrier) (hx : ∀ j, IsClosed {x j}) :
    ∃ π : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m,
      π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap ∧ IsFinite π ∧
      ∀ j, (π.stalkMap (x j)).hom.FormallyUnramified := by
  let p j := pointOfClosedPoint X.structureMap (x j) (hx j)
  have hp : ∀ j, p j ≫ X.structureMap = 𝟙 _ := fun j => pointOfClosedPoint_comp _ _ _
  obtain ⟨π, hover, hfinite, hπ⟩ := exists_points X m p hp
  refine ⟨π, hover, hfinite, fun j => ?_⟩
  have he : p j (IsLocalRing.closedPoint ℂ) = x j := pointOfClosedPoint_apply _ _ _ _
  exact Eq.mp (congrArg (fun y => (π.stalkMap y).hom.FormallyUnramified) he) (hπ j)

end Finite

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.StalkUnramified
