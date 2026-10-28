import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints
import OAI.AlgebraicGeometry.Albanese.Construction.Smooth
import OAI.Geometry.ComplexTorus.RiemannProjectivity.Fin

/-! # Group From -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints

noncomputable section

/-! # RiemannProjectivity: algebraic operations satisfying the torus laws form a commutative group scheme -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

local instance tensor_smooth (X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (X ⊗ Y).hom := by dsimp; infer_instance

local instance unit_smooth : Smooth (𝟙_ (Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).hom := by dsimp; infer_instance

local instance base_smooth : Smooth (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).hom :=
  inferInstanceAs (Smooth (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))

local instance reduced_of_smooth (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] : IsReduced X.left :=
  AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced X.hom

variable {T : Type*} [AddCommGroup T]
  (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsProper X.hom]
  (e : T ≃ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

omit [Smooth X.hom] [IsProper X.hom] in
theorem unit_precomp (r : 𝟙_ (Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ 𝟙_ (Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    r ≫ p = p := by
  rw [toUnit_unique r (𝟙 _), Category.id_comp]

variable (μ : X ⊗ X ⟶ X)
  (hμ : ∀ p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ X), p ≫ μ = e (e.symm (p ≫ fst X X) + e.symm (p ≫ snd X X)))

include hμ

set_option backward.isDefEq.respectTransparency false in
theorem point_one_mul : (e 0 : 𝟙_ (Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X) ▷ X ≫ μ = (λ_ X).hom := by
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  rw [← Category.assoc, hμ]
  simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd, leftUnitor_hom]
  have hzero : p ≫ fst (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) X ≫ e 0 = e 0 := by
    rw [← Category.assoc, unit_precomp]
  rw [hzero, e.symm_apply_apply, zero_add, e.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem point_mul_one : X ◁ (e 0 : 𝟙_ (Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X) ≫ μ = (ρ_ X).hom := by
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  rw [← Category.assoc, hμ]
  simp only [Category.assoc, whiskerLeft_fst, whiskerLeft_snd, rightUnitor_hom]
  have hzero : p ≫ snd X (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) ≫ e 0 = e 0 := by
    rw [← Category.assoc, unit_precomp]
  rw [hzero, e.symm_apply_apply, add_zero, e.apply_symm_apply]
  rfl

theorem point_mul_assoc : (μ ▷ X) ≫ μ = (α_ X X X).hom ≫ (X ◁ μ) ≫ μ := by
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  have hl : p ≫ (μ ▷ X) ≫ μ =
      e ((e.symm (p ≫ fst (X ⊗ X) X ≫ fst X X) + e.symm (p ≫ fst (X ⊗ X) X ≫ snd X X)) +
        e.symm (p ≫ snd (X ⊗ X) X)) := by
    rw [← Category.assoc, hμ]
    simp only [Category.assoc, whiskerRight_fst, whiskerRight_snd]
    rw [← Category.assoc p (fst (X ⊗ X) X) μ, hμ, e.symm_apply_apply]
    rfl
  have hr : p ≫ (α_ X X X).hom ≫ (X ◁ μ) ≫ μ =
      e (e.symm (p ≫ fst (X ⊗ X) X ≫ fst X X) +
        (e.symm (p ≫ fst (X ⊗ X) X ≫ snd X X) + e.symm (p ≫ snd (X ⊗ X) X))) := by
    rw [← Category.assoc p (α_ X X X).hom, ← Category.assoc, hμ]
    simp only [Category.assoc, whiskerLeft_fst, whiskerLeft_snd, associator_hom_fst]
    rw [← Category.assoc p (α_ X X X).hom, ← Category.assoc (p ≫ (α_ X X X).hom)
      (snd X (X ⊗ X)) μ, hμ, e.symm_apply_apply]
    simp only [Category.assoc, associator_hom_snd_fst, associator_hom_snd_snd]
  rw [hl, hr, add_assoc]

@[instance_reducible]
def monoid : MonObj X where
  one := e 0
  mul := μ
  one_mul := point_one_mul X e μ hμ
  mul_one := point_mul_one X e μ hμ
  mul_assoc := point_mul_assoc X e μ hμ

theorem point_comm : (β_ X X).hom ≫ μ = μ := by
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  rw [← Category.assoc, hμ, hμ]
  simp only [Category.assoc, braiding_hom_fst, braiding_hom_snd]
  rw [add_comm]

variable (ν : X ⟶ X) (hν : ∀ p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, p ≫ ν = e (-e.symm p))
include hν

theorem point_left_inv : lift ν (𝟙 X) ≫ μ = toUnit X ≫ e 0 := by
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  rw [← Category.assoc, hμ]
  simp only [Category.assoc, lift_fst, lift_snd, Category.comp_id]
  rw [hν, e.symm_apply_apply, neg_add_cancel, ← Category.assoc, unit_precomp]

theorem point_right_inv : lift (𝟙 X) ν ≫ μ = toUnit X ≫ e 0 := by
  apply AlgebraicGeometry.Albanese.Construction.ClosedPoints.hom_ext_of_points
  intro p
  rw [← Category.assoc, hμ]
  simp only [Category.assoc, lift_fst, lift_snd, Category.comp_id]
  rw [hν, e.symm_apply_apply, add_neg_cancel, ← Category.assoc, unit_precomp]

@[instance_reducible]
def group : GrpObj X where
  toMonObj := monoid X e μ hμ
  inv := ν
  left_inv := point_left_inv X e μ hμ ν hν
  right_inv := point_right_inv X e μ hμ ν hν

theorem commutative : letI : GrpObj X := group X e μ hμ ν hν; IsCommMonObj X := by
  let : GrpObj X := group X e μ hμ ν hν
  exact ⟨point_comm X e μ hμ⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.GroupFrom.Constructions.GroupFromPoints
