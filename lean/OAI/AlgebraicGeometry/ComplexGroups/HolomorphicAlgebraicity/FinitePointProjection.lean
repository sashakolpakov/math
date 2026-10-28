import OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointClosedMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite Point Projection -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePointProjection.Constructions.Algebraization

noncomputable section

/-!
# Finite morphisms detected by injectivity on complex points

For a separated morphism of finite type over the complex numbers, injectivity
on complex points makes the diagonal surjective: its closed image contains
all closed points. Properness then makes the morphism finite.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Set

theorem surjective_of_surjective_complex_points
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (hclosed : IsClosed (range f.left))
    (hpoints : Function.Surjective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)) : Surjective f.left := by
  let : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hsub : closedPoints Y.left ⊆ range f.left := by
    intro y hy
    let q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y :=
      Over.homMk (pointOfClosedPoint Y.hom y hy) (pointOfClosedPoint_comp Y.hom y hy)
    obtain ⟨p, hp⟩ := hpoints q
    refine ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, ?_⟩
    have h := congrArg ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying hp
    change f.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p) =
      pointOfClosedPoint Y.hom y hy ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.basePoint at h
    exact h.trans (pointOfClosedPoint_apply (K := ℂ) Y.hom y hy _)
  have hr : range f.left = univ := by
    apply subset_antisymm (subset_univ _)
    rw [← closure_closedPoints (X := Y.left)]
    exact closure_minimal hsub hclosed
  exact ⟨range_eq_univ.mp hr⟩

theorem universallyInjective_of_injective_complex_points
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [LocallyOfFiniteType f.left] [IsSeparated f.left]
    (hpoints : Function.Injective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)) : UniversallyInjective f.left := by
  let T := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackOver f f
  let δ : X ⟶ T := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackLift f f (𝟙 X) (𝟙 X) rfl
  have hT : LocallyOfFiniteType T.hom := by
    change LocallyOfFiniteType (pullback.snd f.left f.left ≫ X.hom)
    infer_instance
  let : LocallyOfFiniteType T.hom := hT
  have hδ : IsClosedImmersion δ.left := by
    change IsClosedImmersion (pullback.diagonal f.left)
    infer_instance
  let : IsClosedImmersion δ.left := hδ
  have hsurj : Function.Surjective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map δ) := by
    intro q
    let a := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f f) q
    let b := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f f) q
    have hab : a = b := by
      apply hpoints
      change (q ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackToLeft f f) ≫ f =
        (q ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullbackToRight f f) ≫ f
      rw [Category.assoc, Category.assoc, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.pullback_condition]
    refine ⟨a, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · change (a.left ≫ pullback.diagonal f.left) ≫ pullback.fst f.left f.left =
        q.left ≫ pullback.fst f.left f.left
      simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      rfl
    · change (a.left ≫ pullback.diagonal f.left) ≫ pullback.snd f.left f.left =
        q.left ≫ pullback.snd f.left f.left
      simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact congrArg Over.Hom.left hab
  have hδsurj : Surjective δ.left :=
    surjective_of_surjective_complex_points δ δ.left.isClosedMap.isClosed_range hsurj
  exact (UniversallyInjective.iff_diagonal f.left).mpr hδsurj

theorem finite_of_proper_injective_complex_points
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (hpoints : Function.Injective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)) : IsFinite f.left := by
  let : UniversallyInjective f.left := universallyInjective_of_injective_complex_points f hpoints
  exact IsFinite.of_isProper_of_locallyQuasiFinite f.left

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePointProjection.Constructions.Algebraization
