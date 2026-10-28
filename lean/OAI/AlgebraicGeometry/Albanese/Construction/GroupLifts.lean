import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Lifts -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.GroupLifts

open _root_.CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {X G : C} [GrpObj G]

/-- Group operations lifted through a monomorphism satisfy the group laws,
because the monomorphism detects equality of the algebraic morphisms. -/
@[instance_reducible]
def groupOfMono (i : X ⟶ G) [Mono i]
    (e : 𝟙_ C ⟶ X) (m : X ⊗ X ⟶ X) (v : X ⟶ X)
    (he : e ≫ i = 1)
    (hm : m ≫ i = (fst X X ≫ i) * (snd X X ≫ i))
    (hv : v ≫ i = i⁻¹) : GrpObj X where
  one := e
  mul := m
  inv := v
  one_mul := by
    apply (cancel_mono i).mp
    simp [Category.assoc, hm, comp_mul, he, leftUnitor_hom]
  mul_one := by
    apply (cancel_mono i).mp
    simp [Category.assoc, hm, comp_mul, he, rightUnitor_hom]
  mul_assoc := by
    apply (cancel_mono i).mp
    simp [Category.assoc, hm, comp_mul, _root_.mul_assoc]
  left_inv := by
    apply (cancel_mono i).mp
    simp [Category.assoc, hm, comp_mul, he, hv]
  right_inv := by
    apply (cancel_mono i).mp
    simp [Category.assoc, hm, comp_mul, he, hv]

/-- The inclusion preserves the lifted group law. -/
theorem groupOfMono_isMonHom (i : X ⟶ G) [Mono i]
    (e : 𝟙_ C ⟶ X) (m : X ⊗ X ⟶ X) (v : X ⟶ X)
    (he : e ≫ i = 1)
    (hm : m ≫ i = (fst X X ≫ i) * (snd X X ≫ i))
    (hv : v ≫ i = i⁻¹) :
    letI := groupOfMono i e m v he hm hv
    IsMonHom i := by
  let _ := groupOfMono i e m v he hm hv
  refine ⟨?_, ?_⟩
  · change e ≫ i = η[G]
    simpa only [one_eq_one] using he
  · change m ≫ i = (i ⊗ₘ i) ≫ μ[G]
    simpa only [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp] using hm

end OAI.AlgebraicGeometry.Albanese.Construction.GroupLifts
