import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Reflection -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction

noncomputable section

/-! Reflecting group laws from specified images of the three group operations. -/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.CategoryTheory.Functor

universe u v w z

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {D : Type w} [Category.{z} D] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (X : C) [GrpObj (F.obj X)]

abbrev groupObjectOfMappedOperations
    (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X) (inv : X ⟶ X)
    (hOne : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (hMul : F.map mul = OplaxMonoidal.δ F X X ≫ μ[F.obj X])
    (hInv : F.map inv = ι[F.obj X])
    (hLeft : Function.Injective (F.map : (𝟙_ C ⊗ X ⟶ X) → _))
    (hRight : Function.Injective (F.map : (X ⊗ 𝟙_ C ⟶ X) → _))
    (hTriple : Function.Injective (F.map : ((X ⊗ X) ⊗ X ⟶ X) → _))
    (hSelf : Function.Injective (F.map : (X ⟶ X) → _)) : GrpObj X where
  one := one
  mul := mul
  inv := inv
  one_mul := hLeft <| by simp [hOne, hMul, ← OplaxMonoidal.δ_natural_left_assoc]
  mul_one := hRight <| by simp [hOne, hMul, ← OplaxMonoidal.δ_natural_right_assoc]
  mul_assoc := hTriple <| by
    simp [hMul, ← OplaxMonoidal.δ_natural_left_assoc, ← OplaxMonoidal.δ_natural_right_assoc]
  left_inv := hSelf <| by
    simp [hOne, hMul, hInv, OplaxMonoidal.η_of_cartesianMonoidalCategory]
  right_inv := hSelf <| by
    simp [hOne, hMul, hInv, OplaxMonoidal.η_of_cartesianMonoidalCategory]

variable (one : 𝟙_ C ⟶ X) (mul : X ⊗ X ⟶ X) (inv : X ⟶ X)
    (hOne : F.map one = OplaxMonoidal.η F ≫ η[F.obj X])
    (hMul : F.map mul = OplaxMonoidal.δ F X X ≫ μ[F.obj X])
    (hInv : F.map inv = ι[F.obj X])
    (hLeft : Function.Injective (F.map : (𝟙_ C ⊗ X ⟶ X) → _))
    (hRight : Function.Injective (F.map : (X ⊗ 𝟙_ C ⟶ X) → _))
    (hTriple : Function.Injective (F.map : ((X ⊗ X) ⊗ X ⟶ X) → _))
    (hSelf : Function.Injective (F.map : (X ⟶ X) → _))

theorem groupObjectOfMappedOperations_image :
    let original : GrpObj (F.obj X) := inferInstance
    letI := groupObjectOfMappedOperations F X one mul inv hOne hMul hInv
      hLeft hRight hTriple hSelf
    Functor.grpObjObj (F := F) (G := X) = original := by
  ext
  change LaxMonoidal.μ F X X ≫ F.map mul = μ[F.obj X]
  simp [hMul]

theorem groupObjectOfMappedOperations_comm [BraidedCategory C] [BraidedCategory D]
    [IsCommMonObj (F.obj X)]
    (hPair : Function.Injective (F.map : (X ⊗ X ⟶ X) → _)) :
    letI := groupObjectOfMappedOperations F X one mul inv hOne hMul hInv
      hLeft hRight hTriple hSelf
    IsCommMonObj X := by
  let := groupObjectOfMappedOperations F X one mul inv hOne hMul hInv
    hLeft hRight hTriple hSelf
  refine { mul_comm := ?_ }
  apply hPair
  change F.map ((β_ X X).hom ≫ mul) = F.map mul
  have hb : F.map (β_ X X).hom ≫ OplaxMonoidal.δ F X X =
      OplaxMonoidal.δ F X X ≫ (β_ (F.obj X) (F.obj X)).hom := by
    ext <;> simp [← F.map_comp]
  rw [F.map_comp, hMul, ← Category.assoc, hb, Category.assoc, IsCommMonObj.mul_comm]

theorem commutative_group_of_iso [BraidedCategory C]
    {A B : C} [GrpObj A] [IsCommMonObj A] (e : A ≅ B) :
    letI := GrpObj.ofIso e
    IsCommMonObj B := by
  let := GrpObj.ofIso e
  refine { mul_comm := ?_ }
  change (β_ B B).hom ≫ (e.inv ⊗ₘ e.inv) ≫ μ[A] ≫ e.hom =
    (e.inv ⊗ₘ e.inv) ≫ μ[A] ≫ e.hom
  rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]

theorem transported_group_iso_isMonHom {A B : C} [GrpObj B] (e : A ≅ B) :
    letI : GrpObj A := GrpObj.ofIso e.symm
    IsMonHom e.hom := by
  let : GrpObj A := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := isMonHom_ofIso e.symm
  exact inferInstanceAs (IsMonHom e.symm.inv)

omit [GrpObj (F.obj X)] in
theorem image_group_iso_isMonHom (Y : D) [GrpObj Y] (e : F.obj X ≅ Y)
    (groupX : GrpObj X)
    (h : letI := groupX; Functor.grpObjObj (F := F) (G := X) = GrpObj.ofIso e.symm) :
    letI := groupX
    letI : GrpObj (F.obj X) := Functor.grpObjObj (F := F)
    IsMonHom e.hom := by
  let := groupX
  change @IsMonHom D _ _ (F.obj X) Y
    (Functor.grpObjObj (F := F) (G := X)).toMonObj _ e.hom
  rw [h]
  exact transported_group_iso_isMonHom e

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GroupReflection.Construction
